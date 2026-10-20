import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Nat.Sqrt

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace EKG
namespace PatternCount

/-- The number of integers strictly between p/3 and p/2 for an odd prime p. -/
def D (p : ℕ) : ℕ := (p-1)/2 - p/3

/-- Composite-base and prime-base upward-crossing labels. Natural square root
is the floor of the real square root, and primeCounting includes its endpoint. -/
def U (p : ℕ) : ℕ :=
  Nat.primeCounting (Nat.sqrt (2*p)) +
    (Nat.primeCounting (p-1) - Nat.primeCounting (2*p/3))

/-- For the relevant primes the grouped subtraction equals the manuscript's
sum followed by subtraction; no natural-number truncation changes the value. -/
theorem U_eq_sum_sub {p : ℕ} (hp : 3 ≤ p) :
    U p = Nat.primeCounting (Nat.sqrt (2*p)) + Nat.primeCounting (p-1) -
      Nat.primeCounting (2*p/3) := by
  have hle : 2*p/3 ≤ p-1 := by omega
  unfold U
  exact (Nat.add_sub_assoc (Nat.monotone_primeCounting hle) _).symm

/- Derived-source change: the upstream native-evaluation proof of
`checked_finite` is replaced by an ordinary kernel proof. This file is
generated deterministically by scripts/generate-pattern-count.py. Its private
support proves a square-root primality decision procedure, validates every
successor of a balanced count table in 64-value blocks, and proves the table
equal to Nat.primeCounting by induction. The final finite inequality is also
checked in 64-value blocks. Nat.Prime, Nat.primeCounting, D, U, and every
upstream theorem statement remain unchanged. -/

private theorem prime_iff_sqrt_fin (n : ℕ) :
    n.Prime ↔ 2 ≤ n ∧
      ∀ d : Fin (Nat.sqrt n + 1), 2 ≤ d.val → ¬ d.val ∣ n := by
  rw [Nat.prime_def_le_sqrt]
  constructor
  · rintro ⟨h2, hdiv⟩
    refine ⟨h2, ?_⟩
    intro d hd
    exact hdiv d.val hd (Nat.lt_succ_iff.mp d.isLt)
  · rintro ⟨h2, hdiv⟩
    refine ⟨h2, ?_⟩
    intro d hd hds
    exact hdiv ⟨d, Nat.lt_succ_iff.mpr hds⟩ hd

/-- The proved square-root decision procedure uses ordinary kernel reduction. -/
private def sqrtDecidablePrime (n : ℕ) : Decidable n.Prime :=
  decidable_of_iff' _ (prime_iff_sqrt_fin n)

private theorem primeCounting_eq_fast (n : ℕ) :
    Nat.primeCounting n = @Nat.count Nat.Prime sqrtDecidablePrime (n+1) := by
  have heq : Nat.decidablePrime = sqrtDecidablePrime := by
    funext n
    exact Subsingleton.elim _ _
  change @Nat.count Nat.Prime Nat.decidablePrime (n+1) = _
  rw [heq]

/-- The explicit instance prevents recurrence checks from using the default
trial-division procedure embedded in an ordinary proposition-level if. -/
private def fastPrimeFlag (n : ℕ) : ℕ :=
  @ite ℕ n.Prime (sqrtDecidablePrime n) 1 0

private theorem fastPrimeFlag_eq (n : ℕ) :
    fastPrimeFlag n = if n.Prime then 1 else 0 := by
  have heq : sqrtDecidablePrime n = Nat.decidablePrime n :=
    Subsingleton.elim _ _
  unfold fastPrimeFlag
  rw [heq]

/-- Untrusted finite data, indexed by a balanced tree of thresholds.
Only pc_correct below connects this table to mathematical prime counting. -/
private def pc (n : ℕ) : ℕ :=
  if n < 1831 then
    if n < 811 then
      if n < 349 then
        if n < 149 then
          if n < 59 then
            if n < 19 then
              if n < 7 then
                if n < 3 then
                  if n < 2 then
                    0
                  else
                    1
                else
                  if n < 5 then
                    2
                  else
                    3
              else
                if n < 13 then
                  if n < 11 then
                    4
                  else
                    5
                else
                  if n < 17 then
                    6
                  else
                    7
            else
              if n < 37 then
                if n < 29 then
                  if n < 23 then
                    8
                  else
                    9
                else
                  if n < 31 then
                    10
                  else
                    11
              else
                if n < 43 then
                  if n < 41 then
                    12
                  else
                    13
                else
                  if n < 47 then
                    14
                  else
                    if n < 53 then
                      15
                    else
                      16
          else
            if n < 101 then
              if n < 73 then
                if n < 67 then
                  if n < 61 then
                    17
                  else
                    18
                else
                  if n < 71 then
                    19
                  else
                    20
              else
                if n < 83 then
                  if n < 79 then
                    21
                  else
                    22
                else
                  if n < 89 then
                    23
                  else
                    if n < 97 then
                      24
                    else
                      25
            else
              if n < 113 then
                if n < 107 then
                  if n < 103 then
                    26
                  else
                    27
                else
                  if n < 109 then
                    28
                  else
                    29
              else
                if n < 131 then
                  if n < 127 then
                    30
                  else
                    31
                else
                  if n < 137 then
                    32
                  else
                    if n < 139 then
                      33
                    else
                      34
        else
          if n < 239 then
            if n < 191 then
              if n < 167 then
                if n < 157 then
                  if n < 151 then
                    35
                  else
                    36
                else
                  if n < 163 then
                    37
                  else
                    38
              else
                if n < 179 then
                  if n < 173 then
                    39
                  else
                    40
                else
                  if n < 181 then
                    41
                  else
                    42
            else
              if n < 211 then
                if n < 197 then
                  if n < 193 then
                    43
                  else
                    44
                else
                  if n < 199 then
                    45
                  else
                    46
              else
                if n < 227 then
                  if n < 223 then
                    47
                  else
                    48
                else
                  if n < 229 then
                    49
                  else
                    if n < 233 then
                      50
                    else
                      51
          else
            if n < 283 then
              if n < 263 then
                if n < 251 then
                  if n < 241 then
                    52
                  else
                    53
                else
                  if n < 257 then
                    54
                  else
                    55
              else
                if n < 271 then
                  if n < 269 then
                    56
                  else
                    57
                else
                  if n < 277 then
                    58
                  else
                    if n < 281 then
                      59
                    else
                      60
            else
              if n < 313 then
                if n < 307 then
                  if n < 293 then
                    61
                  else
                    62
                else
                  if n < 311 then
                    63
                  else
                    64
              else
                if n < 331 then
                  if n < 317 then
                    65
                  else
                    66
                else
                  if n < 337 then
                    67
                  else
                    if n < 347 then
                      68
                    else
                      69
      else
        if n < 571 then
          if n < 449 then
            if n < 397 then
              if n < 373 then
                if n < 359 then
                  if n < 353 then
                    70
                  else
                    71
                else
                  if n < 367 then
                    72
                  else
                    73
              else
                if n < 383 then
                  if n < 379 then
                    74
                  else
                    75
                else
                  if n < 389 then
                    76
                  else
                    77
            else
              if n < 421 then
                if n < 409 then
                  if n < 401 then
                    78
                  else
                    79
                else
                  if n < 419 then
                    80
                  else
                    81
              else
                if n < 433 then
                  if n < 431 then
                    82
                  else
                    83
                else
                  if n < 439 then
                    84
                  else
                    if n < 443 then
                      85
                    else
                      86
          else
            if n < 503 then
              if n < 467 then
                if n < 461 then
                  if n < 457 then
                    87
                  else
                    88
                else
                  if n < 463 then
                    89
                  else
                    90
              else
                if n < 487 then
                  if n < 479 then
                    91
                  else
                    92
                else
                  if n < 491 then
                    93
                  else
                    if n < 499 then
                      94
                    else
                      95
            else
              if n < 541 then
                if n < 521 then
                  if n < 509 then
                    96
                  else
                    97
                else
                  if n < 523 then
                    98
                  else
                    99
              else
                if n < 557 then
                  if n < 547 then
                    100
                  else
                    101
                else
                  if n < 563 then
                    102
                  else
                    if n < 569 then
                      103
                    else
                      104
        else
          if n < 677 then
            if n < 619 then
              if n < 599 then
                if n < 587 then
                  if n < 577 then
                    105
                  else
                    106
                else
                  if n < 593 then
                    107
                  else
                    108
              else
                if n < 607 then
                  if n < 601 then
                    109
                  else
                    110
                else
                  if n < 613 then
                    111
                  else
                    if n < 617 then
                      112
                    else
                      113
            else
              if n < 647 then
                if n < 641 then
                  if n < 631 then
                    114
                  else
                    115
                else
                  if n < 643 then
                    116
                  else
                    117
              else
                if n < 659 then
                  if n < 653 then
                    118
                  else
                    119
                else
                  if n < 661 then
                    120
                  else
                    if n < 673 then
                      121
                    else
                      122
          else
            if n < 743 then
              if n < 709 then
                if n < 691 then
                  if n < 683 then
                    123
                  else
                    124
                else
                  if n < 701 then
                    125
                  else
                    126
              else
                if n < 727 then
                  if n < 719 then
                    127
                  else
                    128
                else
                  if n < 733 then
                    129
                  else
                    if n < 739 then
                      130
                    else
                      131
            else
              if n < 769 then
                if n < 757 then
                  if n < 751 then
                    132
                  else
                    133
                else
                  if n < 761 then
                    134
                  else
                    135
              else
                if n < 787 then
                  if n < 773 then
                    136
                  else
                    137
                else
                  if n < 797 then
                    138
                  else
                    if n < 809 then
                      139
                    else
                      140
    else
      if n < 1297 then
        if n < 1049 then
          if n < 929 then
            if n < 859 then
              if n < 829 then
                if n < 823 then
                  if n < 821 then
                    141
                  else
                    142
                else
                  if n < 827 then
                    143
                  else
                    144
              else
                if n < 853 then
                  if n < 839 then
                    145
                  else
                    146
                else
                  if n < 857 then
                    147
                  else
                    148
            else
              if n < 883 then
                if n < 877 then
                  if n < 863 then
                    149
                  else
                    150
                else
                  if n < 881 then
                    151
                  else
                    152
              else
                if n < 907 then
                  if n < 887 then
                    153
                  else
                    154
                else
                  if n < 911 then
                    155
                  else
                    if n < 919 then
                      156
                    else
                      157
          else
            if n < 991 then
              if n < 953 then
                if n < 941 then
                  if n < 937 then
                    158
                  else
                    159
                else
                  if n < 947 then
                    160
                  else
                    161
              else
                if n < 971 then
                  if n < 967 then
                    162
                  else
                    163
                else
                  if n < 977 then
                    164
                  else
                    if n < 983 then
                      165
                    else
                      166
            else
              if n < 1019 then
                if n < 1009 then
                  if n < 997 then
                    167
                  else
                    168
                else
                  if n < 1013 then
                    169
                  else
                    170
              else
                if n < 1031 then
                  if n < 1021 then
                    171
                  else
                    172
                else
                  if n < 1033 then
                    173
                  else
                    if n < 1039 then
                      174
                    else
                      175
        else
          if n < 1171 then
            if n < 1097 then
              if n < 1069 then
                if n < 1061 then
                  if n < 1051 then
                    176
                  else
                    177
                else
                  if n < 1063 then
                    178
                  else
                    179
              else
                if n < 1091 then
                  if n < 1087 then
                    180
                  else
                    181
                else
                  if n < 1093 then
                    182
                  else
                    183
            else
              if n < 1123 then
                if n < 1109 then
                  if n < 1103 then
                    184
                  else
                    185
                else
                  if n < 1117 then
                    186
                  else
                    187
              else
                if n < 1151 then
                  if n < 1129 then
                    188
                  else
                    189
                else
                  if n < 1153 then
                    190
                  else
                    if n < 1163 then
                      191
                    else
                      192
          else
            if n < 1231 then
              if n < 1201 then
                if n < 1187 then
                  if n < 1181 then
                    193
                  else
                    194
                else
                  if n < 1193 then
                    195
                  else
                    196
              else
                if n < 1217 then
                  if n < 1213 then
                    197
                  else
                    198
                else
                  if n < 1223 then
                    199
                  else
                    if n < 1229 then
                      200
                    else
                      201
            else
              if n < 1277 then
                if n < 1249 then
                  if n < 1237 then
                    202
                  else
                    203
                else
                  if n < 1259 then
                    204
                  else
                    205
              else
                if n < 1283 then
                  if n < 1279 then
                    206
                  else
                    207
                else
                  if n < 1289 then
                    208
                  else
                    if n < 1291 then
                      209
                    else
                      210
      else
        if n < 1559 then
          if n < 1439 then
            if n < 1367 then
              if n < 1319 then
                if n < 1303 then
                  if n < 1301 then
                    211
                  else
                    212
                else
                  if n < 1307 then
                    213
                  else
                    214
              else
                if n < 1327 then
                  if n < 1321 then
                    215
                  else
                    216
                else
                  if n < 1361 then
                    217
                  else
                    218
            else
              if n < 1409 then
                if n < 1381 then
                  if n < 1373 then
                    219
                  else
                    220
                else
                  if n < 1399 then
                    221
                  else
                    222
              else
                if n < 1427 then
                  if n < 1423 then
                    223
                  else
                    224
                else
                  if n < 1429 then
                    225
                  else
                    if n < 1433 then
                      226
                    else
                      227
          else
            if n < 1489 then
              if n < 1459 then
                if n < 1451 then
                  if n < 1447 then
                    228
                  else
                    229
                else
                  if n < 1453 then
                    230
                  else
                    231
              else
                if n < 1481 then
                  if n < 1471 then
                    232
                  else
                    233
                else
                  if n < 1483 then
                    234
                  else
                    if n < 1487 then
                      235
                    else
                      236
            else
              if n < 1523 then
                if n < 1499 then
                  if n < 1493 then
                    237
                  else
                    238
                else
                  if n < 1511 then
                    239
                  else
                    240
              else
                if n < 1543 then
                  if n < 1531 then
                    241
                  else
                    242
                else
                  if n < 1549 then
                    243
                  else
                    if n < 1553 then
                      244
                    else
                      245
        else
          if n < 1693 then
            if n < 1613 then
              if n < 1583 then
                if n < 1571 then
                  if n < 1567 then
                    246
                  else
                    247
                else
                  if n < 1579 then
                    248
                  else
                    249
              else
                if n < 1601 then
                  if n < 1597 then
                    250
                  else
                    251
                else
                  if n < 1607 then
                    252
                  else
                    if n < 1609 then
                      253
                    else
                      254
            else
              if n < 1637 then
                if n < 1621 then
                  if n < 1619 then
                    255
                  else
                    256
                else
                  if n < 1627 then
                    257
                  else
                    258
              else
                if n < 1663 then
                  if n < 1657 then
                    259
                  else
                    260
                else
                  if n < 1667 then
                    261
                  else
                    if n < 1669 then
                      262
                    else
                      263
          else
            if n < 1753 then
              if n < 1721 then
                if n < 1699 then
                  if n < 1697 then
                    264
                  else
                    265
                else
                  if n < 1709 then
                    266
                  else
                    267
              else
                if n < 1733 then
                  if n < 1723 then
                    268
                  else
                    269
                else
                  if n < 1741 then
                    270
                  else
                    if n < 1747 then
                      271
                    else
                      272
            else
              if n < 1787 then
                if n < 1777 then
                  if n < 1759 then
                    273
                  else
                    274
                else
                  if n < 1783 then
                    275
                  else
                    276
              else
                if n < 1801 then
                  if n < 1789 then
                    277
                  else
                    278
                else
                  if n < 1811 then
                    279
                  else
                    if n < 1823 then
                      280
                    else
                      281
  else
    if n < 2927 then
      if n < 2377 then
        if n < 2099 then
          if n < 1979 then
            if n < 1889 then
              if n < 1871 then
                if n < 1861 then
                  if n < 1847 then
                    282
                  else
                    283
                else
                  if n < 1867 then
                    284
                  else
                    285
              else
                if n < 1877 then
                  if n < 1873 then
                    286
                  else
                    287
                else
                  if n < 1879 then
                    288
                  else
                    289
            else
              if n < 1931 then
                if n < 1907 then
                  if n < 1901 then
                    290
                  else
                    291
                else
                  if n < 1913 then
                    292
                  else
                    293
              else
                if n < 1949 then
                  if n < 1933 then
                    294
                  else
                    295
                else
                  if n < 1951 then
                    296
                  else
                    if n < 1973 then
                      297
                    else
                      298
          else
            if n < 2029 then
              if n < 1999 then
                if n < 1993 then
                  if n < 1987 then
                    299
                  else
                    300
                else
                  if n < 1997 then
                    301
                  else
                    302
              else
                if n < 2011 then
                  if n < 2003 then
                    303
                  else
                    304
                else
                  if n < 2017 then
                    305
                  else
                    if n < 2027 then
                      306
                    else
                      307
            else
              if n < 2069 then
                if n < 2053 then
                  if n < 2039 then
                    308
                  else
                    309
                else
                  if n < 2063 then
                    310
                  else
                    311
              else
                if n < 2083 then
                  if n < 2081 then
                    312
                  else
                    313
                else
                  if n < 2087 then
                    314
                  else
                    if n < 2089 then
                      315
                    else
                      316
        else
          if n < 2243 then
            if n < 2153 then
              if n < 2131 then
                if n < 2113 then
                  if n < 2111 then
                    317
                  else
                    318
                else
                  if n < 2129 then
                    319
                  else
                    320
              else
                if n < 2141 then
                  if n < 2137 then
                    321
                  else
                    322
                else
                  if n < 2143 then
                    323
                  else
                    324
            else
              if n < 2207 then
                if n < 2179 then
                  if n < 2161 then
                    325
                  else
                    326
                else
                  if n < 2203 then
                    327
                  else
                    328
              else
                if n < 2221 then
                  if n < 2213 then
                    329
                  else
                    330
                else
                  if n < 2237 then
                    331
                  else
                    if n < 2239 then
                      332
                    else
                      333
          else
            if n < 2309 then
              if n < 2273 then
                if n < 2267 then
                  if n < 2251 then
                    334
                  else
                    335
                else
                  if n < 2269 then
                    336
                  else
                    337
              else
                if n < 2287 then
                  if n < 2281 then
                    338
                  else
                    339
                else
                  if n < 2293 then
                    340
                  else
                    if n < 2297 then
                      341
                    else
                      342
            else
              if n < 2341 then
                if n < 2333 then
                  if n < 2311 then
                    343
                  else
                    344
                else
                  if n < 2339 then
                    345
                  else
                    346
              else
                if n < 2351 then
                  if n < 2347 then
                    347
                  else
                    348
                else
                  if n < 2357 then
                    349
                  else
                    if n < 2371 then
                      350
                    else
                      351
      else
        if n < 2671 then
          if n < 2521 then
            if n < 2423 then
              if n < 2393 then
                if n < 2383 then
                  if n < 2381 then
                    352
                  else
                    353
                else
                  if n < 2389 then
                    354
                  else
                    355
              else
                if n < 2411 then
                  if n < 2399 then
                    356
                  else
                    357
                else
                  if n < 2417 then
                    358
                  else
                    359
            else
              if n < 2459 then
                if n < 2441 then
                  if n < 2437 then
                    360
                  else
                    361
                else
                  if n < 2447 then
                    362
                  else
                    363
              else
                if n < 2473 then
                  if n < 2467 then
                    364
                  else
                    365
                else
                  if n < 2477 then
                    366
                  else
                    if n < 2503 then
                      367
                    else
                      368
          else
            if n < 2593 then
              if n < 2549 then
                if n < 2539 then
                  if n < 2531 then
                    369
                  else
                    370
                else
                  if n < 2543 then
                    371
                  else
                    372
              else
                if n < 2557 then
                  if n < 2551 then
                    373
                  else
                    374
                else
                  if n < 2579 then
                    375
                  else
                    if n < 2591 then
                      376
                    else
                      377
            else
              if n < 2633 then
                if n < 2617 then
                  if n < 2609 then
                    378
                  else
                    379
                else
                  if n < 2621 then
                    380
                  else
                    381
              else
                if n < 2657 then
                  if n < 2647 then
                    382
                  else
                    383
                else
                  if n < 2659 then
                    384
                  else
                    if n < 2663 then
                      385
                    else
                      386
        else
          if n < 2789 then
            if n < 2713 then
              if n < 2689 then
                if n < 2683 then
                  if n < 2677 then
                    387
                  else
                    388
                else
                  if n < 2687 then
                    389
                  else
                    390
              else
                if n < 2699 then
                  if n < 2693 then
                    391
                  else
                    392
                else
                  if n < 2707 then
                    393
                  else
                    if n < 2711 then
                      394
                    else
                      395
            else
              if n < 2741 then
                if n < 2729 then
                  if n < 2719 then
                    396
                  else
                    397
                else
                  if n < 2731 then
                    398
                  else
                    399
              else
                if n < 2753 then
                  if n < 2749 then
                    400
                  else
                    401
                else
                  if n < 2767 then
                    402
                  else
                    if n < 2777 then
                      403
                    else
                      404
          else
            if n < 2851 then
              if n < 2803 then
                if n < 2797 then
                  if n < 2791 then
                    405
                  else
                    406
                else
                  if n < 2801 then
                    407
                  else
                    408
              else
                if n < 2833 then
                  if n < 2819 then
                    409
                  else
                    410
                else
                  if n < 2837 then
                    411
                  else
                    if n < 2843 then
                      412
                    else
                      413
            else
              if n < 2887 then
                if n < 2861 then
                  if n < 2857 then
                    414
                  else
                    415
                else
                  if n < 2879 then
                    416
                  else
                    417
              else
                if n < 2903 then
                  if n < 2897 then
                    418
                  else
                    419
                else
                  if n < 2909 then
                    420
                  else
                    if n < 2917 then
                      421
                    else
                      422
    else
      if n < 3533 then
        if n < 3251 then
          if n < 3079 then
            if n < 3001 then
              if n < 2963 then
                if n < 2953 then
                  if n < 2939 then
                    423
                  else
                    424
                else
                  if n < 2957 then
                    425
                  else
                    426
              else
                if n < 2971 then
                  if n < 2969 then
                    427
                  else
                    428
                else
                  if n < 2999 then
                    429
                  else
                    430
            else
              if n < 3037 then
                if n < 3019 then
                  if n < 3011 then
                    431
                  else
                    432
                else
                  if n < 3023 then
                    433
                  else
                    434
              else
                if n < 3049 then
                  if n < 3041 then
                    435
                  else
                    436
                else
                  if n < 3061 then
                    437
                  else
                    if n < 3067 then
                      438
                    else
                      439
          else
            if n < 3169 then
              if n < 3119 then
                if n < 3089 then
                  if n < 3083 then
                    440
                  else
                    441
                else
                  if n < 3109 then
                    442
                  else
                    443
              else
                if n < 3137 then
                  if n < 3121 then
                    444
                  else
                    445
                else
                  if n < 3163 then
                    446
                  else
                    if n < 3167 then
                      447
                    else
                      448
            else
              if n < 3203 then
                if n < 3187 then
                  if n < 3181 then
                    449
                  else
                    450
                else
                  if n < 3191 then
                    451
                  else
                    452
              else
                if n < 3217 then
                  if n < 3209 then
                    453
                  else
                    454
                else
                  if n < 3221 then
                    455
                  else
                    if n < 3229 then
                      456
                    else
                      457
        else
          if n < 3373 then
            if n < 3319 then
              if n < 3271 then
                if n < 3257 then
                  if n < 3253 then
                    458
                  else
                    459
                else
                  if n < 3259 then
                    460
                  else
                    461
              else
                if n < 3301 then
                  if n < 3299 then
                    462
                  else
                    463
                else
                  if n < 3307 then
                    464
                  else
                    if n < 3313 then
                      465
                    else
                      466
            else
              if n < 3343 then
                if n < 3329 then
                  if n < 3323 then
                    467
                  else
                    468
                else
                  if n < 3331 then
                    469
                  else
                    470
              else
                if n < 3359 then
                  if n < 3347 then
                    471
                  else
                    472
                else
                  if n < 3361 then
                    473
                  else
                    if n < 3371 then
                      474
                    else
                      475
          else
            if n < 3463 then
              if n < 3413 then
                if n < 3391 then
                  if n < 3389 then
                    476
                  else
                    477
                else
                  if n < 3407 then
                    478
                  else
                    479
              else
                if n < 3449 then
                  if n < 3433 then
                    480
                  else
                    481
                else
                  if n < 3457 then
                    482
                  else
                    if n < 3461 then
                      483
                    else
                      484
            else
              if n < 3499 then
                if n < 3469 then
                  if n < 3467 then
                    485
                  else
                    486
                else
                  if n < 3491 then
                    487
                  else
                    488
              else
                if n < 3517 then
                  if n < 3511 then
                    489
                  else
                    490
                else
                  if n < 3527 then
                    491
                  else
                    if n < 3529 then
                      492
                    else
                      493
      else
        if n < 3803 then
          if n < 3659 then
            if n < 3583 then
              if n < 3557 then
                if n < 3541 then
                  if n < 3539 then
                    494
                  else
                    495
                else
                  if n < 3547 then
                    496
                  else
                    497
              else
                if n < 3571 then
                  if n < 3559 then
                    498
                  else
                    499
                else
                  if n < 3581 then
                    500
                  else
                    501
            else
              if n < 3617 then
                if n < 3607 then
                  if n < 3593 then
                    502
                  else
                    503
                else
                  if n < 3613 then
                    504
                  else
                    505
              else
                if n < 3631 then
                  if n < 3623 then
                    506
                  else
                    507
                else
                  if n < 3637 then
                    508
                  else
                    if n < 3643 then
                      509
                    else
                      510
          else
            if n < 3727 then
              if n < 3691 then
                if n < 3673 then
                  if n < 3671 then
                    511
                  else
                    512
                else
                  if n < 3677 then
                    513
                  else
                    514
              else
                if n < 3701 then
                  if n < 3697 then
                    515
                  else
                    516
                else
                  if n < 3709 then
                    517
                  else
                    if n < 3719 then
                      518
                    else
                      519
            else
              if n < 3767 then
                if n < 3739 then
                  if n < 3733 then
                    520
                  else
                    521
                else
                  if n < 3761 then
                    522
                  else
                    523
              else
                if n < 3779 then
                  if n < 3769 then
                    524
                  else
                    525
                else
                  if n < 3793 then
                    526
                  else
                    if n < 3797 then
                      527
                    else
                      528
        else
          if n < 3943 then
            if n < 3881 then
              if n < 3847 then
                if n < 3823 then
                  if n < 3821 then
                    529
                  else
                    530
                else
                  if n < 3833 then
                    531
                  else
                    532
              else
                if n < 3853 then
                  if n < 3851 then
                    533
                  else
                    534
                else
                  if n < 3863 then
                    535
                  else
                    if n < 3877 then
                      536
                    else
                      537
            else
              if n < 3917 then
                if n < 3907 then
                  if n < 3889 then
                    538
                  else
                    539
                else
                  if n < 3911 then
                    540
                  else
                    541
              else
                if n < 3923 then
                  if n < 3919 then
                    542
                  else
                    543
                else
                  if n < 3929 then
                    544
                  else
                    if n < 3931 then
                      545
                    else
                      546
          else
            if n < 4021 then
              if n < 4001 then
                if n < 3967 then
                  if n < 3947 then
                    547
                  else
                    548
                else
                  if n < 3989 then
                    549
                  else
                    550
              else
                if n < 4007 then
                  if n < 4003 then
                    551
                  else
                    552
                else
                  if n < 4013 then
                    553
                  else
                    if n < 4019 then
                      554
                    else
                      555
            else
              if n < 4057 then
                if n < 4049 then
                  if n < 4027 then
                    556
                  else
                    557
                else
                  if n < 4051 then
                    558
                  else
                    559
              else
                if n < 4079 then
                  if n < 4073 then
                    560
                  else
                    561
                else
                  if n < 4091 then
                    562
                  else
                    if n < 4093 then
                      563
                    else
                      564

private theorem pc_zero : pc 0 = 0 := by decide +kernel

private def RecurrenceBlock (b : ℕ) : Prop :=
  ∀ i : Fin 64,
    pc (64*b + i.val + 1) =
      pc (64*b + i.val) + fastPrimeFlag (64*b + i.val + 1)

private theorem recurrence_block_0 : RecurrenceBlock 0 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_1 : RecurrenceBlock 1 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_2 : RecurrenceBlock 2 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_3 : RecurrenceBlock 3 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_4 : RecurrenceBlock 4 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_5 : RecurrenceBlock 5 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_6 : RecurrenceBlock 6 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_7 : RecurrenceBlock 7 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_8 : RecurrenceBlock 8 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_9 : RecurrenceBlock 9 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_10 : RecurrenceBlock 10 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_11 : RecurrenceBlock 11 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_12 : RecurrenceBlock 12 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_13 : RecurrenceBlock 13 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_14 : RecurrenceBlock 14 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_15 : RecurrenceBlock 15 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_16 : RecurrenceBlock 16 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_17 : RecurrenceBlock 17 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_18 : RecurrenceBlock 18 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_19 : RecurrenceBlock 19 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_20 : RecurrenceBlock 20 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_21 : RecurrenceBlock 21 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_22 : RecurrenceBlock 22 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_23 : RecurrenceBlock 23 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_24 : RecurrenceBlock 24 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_25 : RecurrenceBlock 25 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_26 : RecurrenceBlock 26 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_27 : RecurrenceBlock 27 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_28 : RecurrenceBlock 28 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_29 : RecurrenceBlock 29 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_30 : RecurrenceBlock 30 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_31 : RecurrenceBlock 31 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_32 : RecurrenceBlock 32 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_33 : RecurrenceBlock 33 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_34 : RecurrenceBlock 34 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_35 : RecurrenceBlock 35 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_36 : RecurrenceBlock 36 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_37 : RecurrenceBlock 37 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_38 : RecurrenceBlock 38 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_39 : RecurrenceBlock 39 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_40 : RecurrenceBlock 40 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_41 : RecurrenceBlock 41 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_42 : RecurrenceBlock 42 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_43 : RecurrenceBlock 43 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_44 : RecurrenceBlock 44 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_45 : RecurrenceBlock 45 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_46 : RecurrenceBlock 46 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_47 : RecurrenceBlock 47 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_48 : RecurrenceBlock 48 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_49 : RecurrenceBlock 49 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_50 : RecurrenceBlock 50 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_51 : RecurrenceBlock 51 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_52 : RecurrenceBlock 52 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_53 : RecurrenceBlock 53 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_54 : RecurrenceBlock 54 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_55 : RecurrenceBlock 55 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_56 : RecurrenceBlock 56 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_57 : RecurrenceBlock 57 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_58 : RecurrenceBlock 58 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_59 : RecurrenceBlock 59 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_60 : RecurrenceBlock 60 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_61 : RecurrenceBlock 61 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_62 : RecurrenceBlock 62 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_block_63 : RecurrenceBlock 63 := by
  unfold RecurrenceBlock
  decide +kernel

private theorem recurrence_blocks (b : ℕ) (hb : b < 64) :
    RecurrenceBlock b := by
  by_cases h32 : b < 32
  ·
    by_cases h16 : b < 16
    ·
      by_cases h8 : b < 8
      ·
        by_cases h4 : b < 4
        ·
          by_cases h2 : b < 2
          ·
            by_cases h1 : b < 1
            ·
              have heq : b = 0 := by omega
              subst b
              exact recurrence_block_0
            ·
              have heq : b = 1 := by omega
              subst b
              exact recurrence_block_1
          ·
            by_cases h3 : b < 3
            ·
              have heq : b = 2 := by omega
              subst b
              exact recurrence_block_2
            ·
              have heq : b = 3 := by omega
              subst b
              exact recurrence_block_3
        ·
          by_cases h6 : b < 6
          ·
            by_cases h5 : b < 5
            ·
              have heq : b = 4 := by omega
              subst b
              exact recurrence_block_4
            ·
              have heq : b = 5 := by omega
              subst b
              exact recurrence_block_5
          ·
            by_cases h7 : b < 7
            ·
              have heq : b = 6 := by omega
              subst b
              exact recurrence_block_6
            ·
              have heq : b = 7 := by omega
              subst b
              exact recurrence_block_7
      ·
        by_cases h12 : b < 12
        ·
          by_cases h10 : b < 10
          ·
            by_cases h9 : b < 9
            ·
              have heq : b = 8 := by omega
              subst b
              exact recurrence_block_8
            ·
              have heq : b = 9 := by omega
              subst b
              exact recurrence_block_9
          ·
            by_cases h11 : b < 11
            ·
              have heq : b = 10 := by omega
              subst b
              exact recurrence_block_10
            ·
              have heq : b = 11 := by omega
              subst b
              exact recurrence_block_11
        ·
          by_cases h14 : b < 14
          ·
            by_cases h13 : b < 13
            ·
              have heq : b = 12 := by omega
              subst b
              exact recurrence_block_12
            ·
              have heq : b = 13 := by omega
              subst b
              exact recurrence_block_13
          ·
            by_cases h15 : b < 15
            ·
              have heq : b = 14 := by omega
              subst b
              exact recurrence_block_14
            ·
              have heq : b = 15 := by omega
              subst b
              exact recurrence_block_15
    ·
      by_cases h24 : b < 24
      ·
        by_cases h20 : b < 20
        ·
          by_cases h18 : b < 18
          ·
            by_cases h17 : b < 17
            ·
              have heq : b = 16 := by omega
              subst b
              exact recurrence_block_16
            ·
              have heq : b = 17 := by omega
              subst b
              exact recurrence_block_17
          ·
            by_cases h19 : b < 19
            ·
              have heq : b = 18 := by omega
              subst b
              exact recurrence_block_18
            ·
              have heq : b = 19 := by omega
              subst b
              exact recurrence_block_19
        ·
          by_cases h22 : b < 22
          ·
            by_cases h21 : b < 21
            ·
              have heq : b = 20 := by omega
              subst b
              exact recurrence_block_20
            ·
              have heq : b = 21 := by omega
              subst b
              exact recurrence_block_21
          ·
            by_cases h23 : b < 23
            ·
              have heq : b = 22 := by omega
              subst b
              exact recurrence_block_22
            ·
              have heq : b = 23 := by omega
              subst b
              exact recurrence_block_23
      ·
        by_cases h28 : b < 28
        ·
          by_cases h26 : b < 26
          ·
            by_cases h25 : b < 25
            ·
              have heq : b = 24 := by omega
              subst b
              exact recurrence_block_24
            ·
              have heq : b = 25 := by omega
              subst b
              exact recurrence_block_25
          ·
            by_cases h27 : b < 27
            ·
              have heq : b = 26 := by omega
              subst b
              exact recurrence_block_26
            ·
              have heq : b = 27 := by omega
              subst b
              exact recurrence_block_27
        ·
          by_cases h30 : b < 30
          ·
            by_cases h29 : b < 29
            ·
              have heq : b = 28 := by omega
              subst b
              exact recurrence_block_28
            ·
              have heq : b = 29 := by omega
              subst b
              exact recurrence_block_29
          ·
            by_cases h31 : b < 31
            ·
              have heq : b = 30 := by omega
              subst b
              exact recurrence_block_30
            ·
              have heq : b = 31 := by omega
              subst b
              exact recurrence_block_31
  ·
    by_cases h48 : b < 48
    ·
      by_cases h40 : b < 40
      ·
        by_cases h36 : b < 36
        ·
          by_cases h34 : b < 34
          ·
            by_cases h33 : b < 33
            ·
              have heq : b = 32 := by omega
              subst b
              exact recurrence_block_32
            ·
              have heq : b = 33 := by omega
              subst b
              exact recurrence_block_33
          ·
            by_cases h35 : b < 35
            ·
              have heq : b = 34 := by omega
              subst b
              exact recurrence_block_34
            ·
              have heq : b = 35 := by omega
              subst b
              exact recurrence_block_35
        ·
          by_cases h38 : b < 38
          ·
            by_cases h37 : b < 37
            ·
              have heq : b = 36 := by omega
              subst b
              exact recurrence_block_36
            ·
              have heq : b = 37 := by omega
              subst b
              exact recurrence_block_37
          ·
            by_cases h39 : b < 39
            ·
              have heq : b = 38 := by omega
              subst b
              exact recurrence_block_38
            ·
              have heq : b = 39 := by omega
              subst b
              exact recurrence_block_39
      ·
        by_cases h44 : b < 44
        ·
          by_cases h42 : b < 42
          ·
            by_cases h41 : b < 41
            ·
              have heq : b = 40 := by omega
              subst b
              exact recurrence_block_40
            ·
              have heq : b = 41 := by omega
              subst b
              exact recurrence_block_41
          ·
            by_cases h43 : b < 43
            ·
              have heq : b = 42 := by omega
              subst b
              exact recurrence_block_42
            ·
              have heq : b = 43 := by omega
              subst b
              exact recurrence_block_43
        ·
          by_cases h46 : b < 46
          ·
            by_cases h45 : b < 45
            ·
              have heq : b = 44 := by omega
              subst b
              exact recurrence_block_44
            ·
              have heq : b = 45 := by omega
              subst b
              exact recurrence_block_45
          ·
            by_cases h47 : b < 47
            ·
              have heq : b = 46 := by omega
              subst b
              exact recurrence_block_46
            ·
              have heq : b = 47 := by omega
              subst b
              exact recurrence_block_47
    ·
      by_cases h56 : b < 56
      ·
        by_cases h52 : b < 52
        ·
          by_cases h50 : b < 50
          ·
            by_cases h49 : b < 49
            ·
              have heq : b = 48 := by omega
              subst b
              exact recurrence_block_48
            ·
              have heq : b = 49 := by omega
              subst b
              exact recurrence_block_49
          ·
            by_cases h51 : b < 51
            ·
              have heq : b = 50 := by omega
              subst b
              exact recurrence_block_50
            ·
              have heq : b = 51 := by omega
              subst b
              exact recurrence_block_51
        ·
          by_cases h54 : b < 54
          ·
            by_cases h53 : b < 53
            ·
              have heq : b = 52 := by omega
              subst b
              exact recurrence_block_52
            ·
              have heq : b = 53 := by omega
              subst b
              exact recurrence_block_53
          ·
            by_cases h55 : b < 55
            ·
              have heq : b = 54 := by omega
              subst b
              exact recurrence_block_54
            ·
              have heq : b = 55 := by omega
              subst b
              exact recurrence_block_55
      ·
        by_cases h60 : b < 60
        ·
          by_cases h58 : b < 58
          ·
            by_cases h57 : b < 57
            ·
              have heq : b = 56 := by omega
              subst b
              exact recurrence_block_56
            ·
              have heq : b = 57 := by omega
              subst b
              exact recurrence_block_57
          ·
            by_cases h59 : b < 59
            ·
              have heq : b = 58 := by omega
              subst b
              exact recurrence_block_58
            ·
              have heq : b = 59 := by omega
              subst b
              exact recurrence_block_59
        ·
          by_cases h62 : b < 62
          ·
            by_cases h61 : b < 61
            ·
              have heq : b = 60 := by omega
              subst b
              exact recurrence_block_60
            ·
              have heq : b = 61 := by omega
              subst b
              exact recurrence_block_61
          ·
            by_cases h63 : b < 63
            ·
              have heq : b = 62 := by omega
              subst b
              exact recurrence_block_62
            ·
              have heq : b = 63 := by omega
              subst b
              exact recurrence_block_63

private theorem pc_recurrence (n : ℕ) (hn : n < 4096) :
    pc (n+1) = pc n + fastPrimeFlag (n+1) := by
  have hb : n / 64 < 64 := by omega
  have hi : n % 64 < 64 := Nat.mod_lt n (by decide)
  have h := recurrence_blocks (n / 64) hb ⟨n % 64, hi⟩
  change pc (64 * (n / 64) + n % 64 + 1) =
    pc (64 * (n / 64) + n % 64) +
      fastPrimeFlag (64 * (n / 64) + n % 64 + 1) at h
  have heq : 64 * (n / 64) + n % 64 = n := by omega
  simpa only [heq] using h

/-- Every table entry in the advertised range is the exact inclusive count.
The argument uses the mathematical count recurrence, not Python primality. -/
private theorem pc_correct : ∀ n : ℕ, n ≤ 4096 → pc n = Nat.primeCounting n := by
  intro n
  induction n with
  | zero =>
      intro _
      simpa only [Nat.primeCounting_zero] using pc_zero
  | succ n ih =>
      intro hn
      rw [pc_recurrence n (by omega), ih (by omega), fastPrimeFlag_eq]
      have hcount : Nat.primeCounting (n+1) = Nat.primeCounting n +
          (if (n+1).Prime then 1 else 0) := by
        simpa only [Nat.primeCounting, Nat.primeCounting'] using
          (Nat.count_succ Nat.Prime (n+1))
      exact hcount.symm

private def TableInequalityBlock (b : ℕ) : Prop :=
  ∀ i : Fin 64, fastPrimeFlag (64*b + i.val) = 1 → 43 < 64*b + i.val →
    pc (Nat.sqrt (2*(64*b + i.val))) +
      (pc (64*b + i.val - 1) - pc (2*(64*b + i.val)/3)) <
        D (64*b + i.val) + 1

private theorem inequality_block_0 : TableInequalityBlock 0 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_1 : TableInequalityBlock 1 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_2 : TableInequalityBlock 2 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_3 : TableInequalityBlock 3 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_4 : TableInequalityBlock 4 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_5 : TableInequalityBlock 5 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_6 : TableInequalityBlock 6 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_7 : TableInequalityBlock 7 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_8 : TableInequalityBlock 8 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_9 : TableInequalityBlock 9 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_10 : TableInequalityBlock 10 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_11 : TableInequalityBlock 11 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_12 : TableInequalityBlock 12 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_13 : TableInequalityBlock 13 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_14 : TableInequalityBlock 14 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_15 : TableInequalityBlock 15 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_16 : TableInequalityBlock 16 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_17 : TableInequalityBlock 17 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_18 : TableInequalityBlock 18 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_19 : TableInequalityBlock 19 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_20 : TableInequalityBlock 20 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_21 : TableInequalityBlock 21 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_22 : TableInequalityBlock 22 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_23 : TableInequalityBlock 23 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_24 : TableInequalityBlock 24 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_25 : TableInequalityBlock 25 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_26 : TableInequalityBlock 26 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_27 : TableInequalityBlock 27 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_28 : TableInequalityBlock 28 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_29 : TableInequalityBlock 29 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_30 : TableInequalityBlock 30 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_31 : TableInequalityBlock 31 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_32 : TableInequalityBlock 32 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_33 : TableInequalityBlock 33 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_34 : TableInequalityBlock 34 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_35 : TableInequalityBlock 35 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_36 : TableInequalityBlock 36 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_37 : TableInequalityBlock 37 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_38 : TableInequalityBlock 38 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_39 : TableInequalityBlock 39 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_40 : TableInequalityBlock 40 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_41 : TableInequalityBlock 41 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_42 : TableInequalityBlock 42 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_43 : TableInequalityBlock 43 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_44 : TableInequalityBlock 44 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_45 : TableInequalityBlock 45 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_46 : TableInequalityBlock 46 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_47 : TableInequalityBlock 47 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_48 : TableInequalityBlock 48 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_49 : TableInequalityBlock 49 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_50 : TableInequalityBlock 50 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_51 : TableInequalityBlock 51 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_52 : TableInequalityBlock 52 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_53 : TableInequalityBlock 53 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_54 : TableInequalityBlock 54 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_55 : TableInequalityBlock 55 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_56 : TableInequalityBlock 56 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_57 : TableInequalityBlock 57 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_58 : TableInequalityBlock 58 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_59 : TableInequalityBlock 59 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_60 : TableInequalityBlock 60 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_61 : TableInequalityBlock 61 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_62 : TableInequalityBlock 62 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_block_63 : TableInequalityBlock 63 := by
  unfold TableInequalityBlock
  decide +kernel

private theorem inequality_blocks (b : ℕ) (hb : b < 64) :
    TableInequalityBlock b := by
  by_cases h32 : b < 32
  ·
    by_cases h16 : b < 16
    ·
      by_cases h8 : b < 8
      ·
        by_cases h4 : b < 4
        ·
          by_cases h2 : b < 2
          ·
            by_cases h1 : b < 1
            ·
              have heq : b = 0 := by omega
              subst b
              exact inequality_block_0
            ·
              have heq : b = 1 := by omega
              subst b
              exact inequality_block_1
          ·
            by_cases h3 : b < 3
            ·
              have heq : b = 2 := by omega
              subst b
              exact inequality_block_2
            ·
              have heq : b = 3 := by omega
              subst b
              exact inequality_block_3
        ·
          by_cases h6 : b < 6
          ·
            by_cases h5 : b < 5
            ·
              have heq : b = 4 := by omega
              subst b
              exact inequality_block_4
            ·
              have heq : b = 5 := by omega
              subst b
              exact inequality_block_5
          ·
            by_cases h7 : b < 7
            ·
              have heq : b = 6 := by omega
              subst b
              exact inequality_block_6
            ·
              have heq : b = 7 := by omega
              subst b
              exact inequality_block_7
      ·
        by_cases h12 : b < 12
        ·
          by_cases h10 : b < 10
          ·
            by_cases h9 : b < 9
            ·
              have heq : b = 8 := by omega
              subst b
              exact inequality_block_8
            ·
              have heq : b = 9 := by omega
              subst b
              exact inequality_block_9
          ·
            by_cases h11 : b < 11
            ·
              have heq : b = 10 := by omega
              subst b
              exact inequality_block_10
            ·
              have heq : b = 11 := by omega
              subst b
              exact inequality_block_11
        ·
          by_cases h14 : b < 14
          ·
            by_cases h13 : b < 13
            ·
              have heq : b = 12 := by omega
              subst b
              exact inequality_block_12
            ·
              have heq : b = 13 := by omega
              subst b
              exact inequality_block_13
          ·
            by_cases h15 : b < 15
            ·
              have heq : b = 14 := by omega
              subst b
              exact inequality_block_14
            ·
              have heq : b = 15 := by omega
              subst b
              exact inequality_block_15
    ·
      by_cases h24 : b < 24
      ·
        by_cases h20 : b < 20
        ·
          by_cases h18 : b < 18
          ·
            by_cases h17 : b < 17
            ·
              have heq : b = 16 := by omega
              subst b
              exact inequality_block_16
            ·
              have heq : b = 17 := by omega
              subst b
              exact inequality_block_17
          ·
            by_cases h19 : b < 19
            ·
              have heq : b = 18 := by omega
              subst b
              exact inequality_block_18
            ·
              have heq : b = 19 := by omega
              subst b
              exact inequality_block_19
        ·
          by_cases h22 : b < 22
          ·
            by_cases h21 : b < 21
            ·
              have heq : b = 20 := by omega
              subst b
              exact inequality_block_20
            ·
              have heq : b = 21 := by omega
              subst b
              exact inequality_block_21
          ·
            by_cases h23 : b < 23
            ·
              have heq : b = 22 := by omega
              subst b
              exact inequality_block_22
            ·
              have heq : b = 23 := by omega
              subst b
              exact inequality_block_23
      ·
        by_cases h28 : b < 28
        ·
          by_cases h26 : b < 26
          ·
            by_cases h25 : b < 25
            ·
              have heq : b = 24 := by omega
              subst b
              exact inequality_block_24
            ·
              have heq : b = 25 := by omega
              subst b
              exact inequality_block_25
          ·
            by_cases h27 : b < 27
            ·
              have heq : b = 26 := by omega
              subst b
              exact inequality_block_26
            ·
              have heq : b = 27 := by omega
              subst b
              exact inequality_block_27
        ·
          by_cases h30 : b < 30
          ·
            by_cases h29 : b < 29
            ·
              have heq : b = 28 := by omega
              subst b
              exact inequality_block_28
            ·
              have heq : b = 29 := by omega
              subst b
              exact inequality_block_29
          ·
            by_cases h31 : b < 31
            ·
              have heq : b = 30 := by omega
              subst b
              exact inequality_block_30
            ·
              have heq : b = 31 := by omega
              subst b
              exact inequality_block_31
  ·
    by_cases h48 : b < 48
    ·
      by_cases h40 : b < 40
      ·
        by_cases h36 : b < 36
        ·
          by_cases h34 : b < 34
          ·
            by_cases h33 : b < 33
            ·
              have heq : b = 32 := by omega
              subst b
              exact inequality_block_32
            ·
              have heq : b = 33 := by omega
              subst b
              exact inequality_block_33
          ·
            by_cases h35 : b < 35
            ·
              have heq : b = 34 := by omega
              subst b
              exact inequality_block_34
            ·
              have heq : b = 35 := by omega
              subst b
              exact inequality_block_35
        ·
          by_cases h38 : b < 38
          ·
            by_cases h37 : b < 37
            ·
              have heq : b = 36 := by omega
              subst b
              exact inequality_block_36
            ·
              have heq : b = 37 := by omega
              subst b
              exact inequality_block_37
          ·
            by_cases h39 : b < 39
            ·
              have heq : b = 38 := by omega
              subst b
              exact inequality_block_38
            ·
              have heq : b = 39 := by omega
              subst b
              exact inequality_block_39
      ·
        by_cases h44 : b < 44
        ·
          by_cases h42 : b < 42
          ·
            by_cases h41 : b < 41
            ·
              have heq : b = 40 := by omega
              subst b
              exact inequality_block_40
            ·
              have heq : b = 41 := by omega
              subst b
              exact inequality_block_41
          ·
            by_cases h43 : b < 43
            ·
              have heq : b = 42 := by omega
              subst b
              exact inequality_block_42
            ·
              have heq : b = 43 := by omega
              subst b
              exact inequality_block_43
        ·
          by_cases h46 : b < 46
          ·
            by_cases h45 : b < 45
            ·
              have heq : b = 44 := by omega
              subst b
              exact inequality_block_44
            ·
              have heq : b = 45 := by omega
              subst b
              exact inequality_block_45
          ·
            by_cases h47 : b < 47
            ·
              have heq : b = 46 := by omega
              subst b
              exact inequality_block_46
            ·
              have heq : b = 47 := by omega
              subst b
              exact inequality_block_47
    ·
      by_cases h56 : b < 56
      ·
        by_cases h52 : b < 52
        ·
          by_cases h50 : b < 50
          ·
            by_cases h49 : b < 49
            ·
              have heq : b = 48 := by omega
              subst b
              exact inequality_block_48
            ·
              have heq : b = 49 := by omega
              subst b
              exact inequality_block_49
          ·
            by_cases h51 : b < 51
            ·
              have heq : b = 50 := by omega
              subst b
              exact inequality_block_50
            ·
              have heq : b = 51 := by omega
              subst b
              exact inequality_block_51
        ·
          by_cases h54 : b < 54
          ·
            by_cases h53 : b < 53
            ·
              have heq : b = 52 := by omega
              subst b
              exact inequality_block_52
            ·
              have heq : b = 53 := by omega
              subst b
              exact inequality_block_53
          ·
            by_cases h55 : b < 55
            ·
              have heq : b = 54 := by omega
              subst b
              exact inequality_block_54
            ·
              have heq : b = 55 := by omega
              subst b
              exact inequality_block_55
      ·
        by_cases h60 : b < 60
        ·
          by_cases h58 : b < 58
          ·
            by_cases h57 : b < 57
            ·
              have heq : b = 56 := by omega
              subst b
              exact inequality_block_56
            ·
              have heq : b = 57 := by omega
              subst b
              exact inequality_block_57
          ·
            by_cases h59 : b < 59
            ·
              have heq : b = 58 := by omega
              subst b
              exact inequality_block_58
            ·
              have heq : b = 59 := by omega
              subst b
              exact inequality_block_59
        ·
          by_cases h62 : b < 62
          ·
            by_cases h61 : b < 61
            ·
              have heq : b = 60 := by omega
              subst b
              exact inequality_block_60
            ·
              have heq : b = 61 := by omega
              subst b
              exact inequality_block_61
          ·
            by_cases h63 : b < 63
            ·
              have heq : b = 62 := by omega
              subst b
              exact inequality_block_62
            ·
              have heq : b = 63 := by omega
              subst b
              exact inequality_block_63

theorem checked_finite : ∀ p : Fin 4096,
    p.val.Prime → 43 < p.val → U p.val < D p.val + 1 := by
  intro p hp hlo
  have hb : p.val / 64 < 64 := by have := p.isLt; omega
  have hi : p.val % 64 < 64 := Nat.mod_lt p.val (by decide)
  have h := inequality_blocks (p.val / 64) hb ⟨p.val % 64, hi⟩
  change fastPrimeFlag (64 * (p.val / 64) + p.val % 64) = 1 →
    43 < 64 * (p.val / 64) + p.val % 64 →
    pc (Nat.sqrt (2 * (64 * (p.val / 64) + p.val % 64))) +
      (pc (64 * (p.val / 64) + p.val % 64 - 1) -
        pc (2 * (64 * (p.val / 64) + p.val % 64) / 3)) <
      D (64 * (p.val / 64) + p.val % 64) + 1 at h
  have heq : 64 * (p.val / 64) + p.val % 64 = p.val := by omega
  rw [heq] at h
  have hsqrt : Nat.sqrt (2*p.val) ≤ 4096 := by
    apply Nat.le_of_lt_succ
    apply Nat.sqrt_lt.mpr
    have := p.isLt
    omega
  have hsub : p.val - 1 ≤ 4096 := by have := p.isLt; omega
  have hdiv : 2*p.val/3 ≤ 4096 := by have := p.isLt; omega
  unfold U
  rw [← pc_correct (Nat.sqrt (2*p.val)) hsqrt,
    ← pc_correct (p.val-1) hsub, ← pc_correct (2*p.val/3) hdiv]
  have hflag : fastPrimeFlag p.val = 1 := by
    rw [fastPrimeFlag_eq, if_pos hp]
  exact h hflag hlo

theorem finite_inequality {p : ℕ} (hp : p.Prime) (hlo : 43 < p)
    (hhi : p < 4096) : U p < D p + 1 :=
  checked_finite ⟨p, hhi⟩ hp hlo

theorem finite_crossing_inequality {p : ℕ} (hp : p.Prime) (hlo : 43 < p)
    (hhi : p < 4096) :
    Nat.primeCounting (Nat.sqrt (2*p)) + Nat.primeCounting (p-1) -
      Nat.primeCounting (2*p/3) < ((p-1)/2 - p/3) + 1 := by
  have h := finite_inequality hp hlo hhi
  rw [U_eq_sum_sub (by omega : 3 ≤ p)] at h
  exact h

end PatternCount
end EKG
