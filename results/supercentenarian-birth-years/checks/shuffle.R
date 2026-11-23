# Use the pinned supplement's own expressions to recover its cell weights.
args <- commandArgs(trailingOnly = TRUE)
data_dir <- args[[1]]
Sys.setlocale("LC_COLLATE", "C")
s1 <- readLines("s1.R", warn = FALSE)
code <- function(lines) parse(text = s1[lines])
eval(code(c(50:64, 74:90, 118:120, 205, 144:146, 219:220)))
us <- which(Pop_birth == "USA")
state <- Pop_birth_subnat[us]
year <- as.integer(Pop_YOB[us])
levels_year <- as.integer(colnames(Supers_stateYear))
kept <- Supers_by_year$State[-c(29, 33)]
stopifnot(length(year) == 697L, !anyNA(year),
          identical(Supers_by_year$State[c(29,33)], c("New York","Oklahoma Territory")))
align_rows <- code(248:255)
recycling <- 0L
withCallingHandlers(eval(align_rows), warning = function(w) {
    if (!grepl("number of columns of result", conditionMessage(w), fixed = TRUE)) stop(w)
    recycling <<- recycling + 1L
    invokeRestart("muffleWarning")
})
stopifnot(recycling == 17L, length(kept) == 44L)
observed <- c(eval(code(273)), eval(code(275)))
stopifnot(all(observed == c(534,112)), ncol(time_vec2) == 123L)

# Pass distinct year indices through S1's same merging, sorting and recycling.
# A copied index contributes once for each occurrence on its side of the split.
Supers_stateYear[,] <- rep(seq_along(levels_year), each = nrow(Supers_stateYear))
suppressWarnings(eval(align_rows))
reg <- Start_reg$Births.all.areas[match(state, Start_reg$State)]
stopifnot(sum(is.na(state)) == 3L, sum(state == "Oklahoma Territory", na.rm = TRUE) == 4L,
          sum(!is.na(reg)) == 690L)
if ("--bounds" %in% args) {
    reg_totals <- as.data.frame(table(reg, useNA = "ifany"))
    year_totals <- as.data.frame(table(year))
    names(reg_totals) <- c("registration", "records")
    names(year_totals) <- c("year", "records")
    write.csv(reg_totals, "registration-totals.csv", row.names = FALSE, na = "")
    write.csv(year_totals, "year-totals.csv", row.names = FALSE)
}
side <- function(columns) {
    weights <- t(apply(time_vec2[, columns, drop = FALSE], 1L, function(row)
        tabulate(as.integer(row), nbins = length(levels_year))))
    slots <- weights[match(state, kept), , drop = FALSE]
    slots[is.na(slots)] <- 0L
    slots
}
early <- side(1:62)
late <- side(63:ncol(time_vec2))
stopifnot(all(early + late == as.integer(state %in% kept)))
registration <- Start_reg$Births.all.areas[match(kept, Start_reg$State)]
cutoffs <- vapply(registration, function(r) sort(unique(c(-60:60, levels_year - r)))[62], integer(1))
stopifnot(identical(sort(unique(cutoffs)), c(-3L, -2L, -1L, 1L)),
          all(table(cutoffs) == c(4, 7, 26, 7)),
          sum(year %in% 1814:1815) == 2L, all(state[year %in% 1814:1815] == "New York"))
index <- match(year, levels_year)
cells <- function(assigned) {
    positions <- cbind(seq_along(year), assigned)
    offset <- levels_year[assigned] - reg
    cbind(s1_before = early[positions], s1_after = late[positions],
          aligned_before = !is.na(offset) & offset >= -60 & offset <= 1,
          aligned_after = !is.na(offset) & offset >= 2 & offset <= 60,
          strictly_before = !is.na(offset) & offset >= -60 & offset < 0,
          through_registration = !is.na(offset) & offset >= -60 & offset <= 0)
}
observed_cells <- cells(index)
expected <- read.csv(file.path(data_dir, "state-counts.csv"), check.names = FALSE)
states <- sort(unique(state[!is.na(reg)]))
stopifnot(identical(states, expected$state))
for (i in seq_along(states)) {
    slots <- which(state == states[i])
    totals <- colSums(observed_cells[slots, 1:4, drop = FALSE])
    stopifnot(all(totals == unlist(expected[i, names(totals)])),
              length(slots) == expected$records[i],
              length(slots) - sum(totals[3:4]) == expected$aligned_outside[i])
}
RNGkind("Mersenne-Twister", "Inversion", "Rejection")
draws <- do.call(cbind, lapply(0:19, function(piece) {
    set.seed(20261122L + piece)
    replicate(500, colSums(cells(index[sample.int(length(index))])))
}))
expected <- read.csv(file.path(data_dir, "shuffle-counts.csv"))
for (method in c("s1", "aligned")) {
    b <- draws[paste0(method, "_before"), ]
    n <- b + draws[paste0(method, "_after"), ]
    freq <- table(paste(b, n))
    rows <- expected[expected$method == method, ]
    keys <- paste(rows$early, rows$eligible)
    stopifnot(!anyDuplicated(keys), setequal(keys, names(freq)), all(freq[keys] == rows$draws))
}
cat("Reproduced 45 state rows and both 10,000-shuffle histograms.\n")

# Post hoc cutoffs use the same assignments and the same eligible records.
eligible <- draws["aligned_before", ] + draws["aligned_after", ]
observed_eligible <- sum(observed_cells[, c("aligned_before", "aligned_after")])
for (method in c("strictly_before", "through_registration")) {
    observed_early <- sum(observed_cells[, method])
    shares <- draws[method, ] / eligible
    # Cross-products give exact comparisons, including ties.
    difference <- draws[method, ] * observed_eligible - observed_early * eligible
    midrank <- mean((difference < 0) + 0.5 * (difference == 0))
    endpoints <- sort(shares)[c(250, 9750)]
    cat(sprintf("%s: %d/%d, interval %.2f%% to %.2f%%, midrank %.2f%%\n",
                method, observed_early, observed_eligible, 100 * endpoints[1],
                100 * endpoints[2], 100 * midrank))
}
