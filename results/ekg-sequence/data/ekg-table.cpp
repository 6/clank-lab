// Exact EKG generation with bounded storage and independent prefix checks.
// Build: g++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -o ekg-table ekg-table.cpp
// Execute: ./ekg-table 100000000 400000000 ekg-table.csv ekg-table-summary.json
// The CSV is numerical evidence, not a proof of an asymptotic limit.
#include <algorithm>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <limits>
#include <numeric>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

using u32 = std::uint32_t;
using u64 = std::uint64_t;

struct Generator {
    u32 bound;
    std::vector<std::uint16_t> odd_spf;
    std::vector<u32> odd_cursor;
    std::vector<u64> used;
    u32 even_cursor = 2;
    explicit Generator(u32 capacity)
        : bound(capacity), odd_spf((u64(capacity) + 1) / 2),
          odd_cursor((u64(capacity) + 1) / 2), used(u64(capacity) / 64 + 1) {
        // Zero denotes an odd prime (apart from index zero, representing 1).
        // Every composite's smallest prime factor is at most sqrt(bound).
        for (u32 p = 3; u64(p) * p <= bound; p += 2) {
            if (odd_spf[p / 2] != 0) continue;
            for (u64 j = u64(p) * p; j <= bound; j += u64(2) * p)
                if (odd_spf[j / 2] == 0) odd_spf[j / 2] = std::uint16_t(p);
        }
    }
    bool occupied(u32 x) const {
        return x <= bound && ((used[x / 64] >> (x % 64)) & 1U);
    }
    void mark(u32 x) {
        if (x == 0 || x > bound || occupied(x))
            throw std::runtime_error("invalid or repeated selection");
        used[x / 64] |= u64(1) << (x % 64);
    }
    bool prime(u32 x) const {
        return x == 2 || (x >= 3 && (x & 1U) && odd_spf[x / 2] == 0);
    }
    u32 available(u32 p) {
        u32& cursor = p == 2 ? even_cursor : odd_cursor[p / 2];
        if (!cursor) cursor = p;
        while (occupied(cursor)) cursor += p;
        // Beyond the bound everything is unused; this cursor is still exact.
        return cursor;
    }
    u32 next(u32 previous) {
        u32 best = std::numeric_limits<u32>::max();
        u32 x = previous;
        if ((x & 1U) == 0) {
            best = available(2);
            do { x /= 2; } while ((x & 1U) == 0);
        }
        while (x > 1) {
            u32 p = odd_spf[x / 2];
            if (!p) p = x;
            best = std::min(best, available(p));
            do { x /= p; } while (x % p == 0);
        }
        if (best > bound)
            throw std::runtime_error("capacity exhausted; increase the bound and restart");
        mark(best);
        return best;
    }
    u64 transform(u32 x) const {
        if (x > 2 && prime(x)) return u64(2) * x;
        if (x % 3 == 0) {
            u32 p = x / 3;
            if (p > 2 && prime(p)) return u64(2) * p;
        }
        return x;
    }
};

// Independent checker: ordered set, direct gcd, and a scan starting at 1.
// It does not call the generator, its bitmap, sieve, or prime cursors.
std::size_t naive_mismatch(const std::vector<u32>& prefix) {
    std::set<u32> seen;
    for (std::size_t i = 0; i < prefix.size(); ++i) {
        u32 expected = i == 0 ? 1 : 2;
        if (i >= 2) {
            expected = 1;
            while (seen.count(expected) || std::gcd(expected, prefix[i - 1]) == 1)
                ++expected;
        }
        if (prefix[i] != expected) return i + 1;
        seen.insert(prefix[i]);
    }
    return 0;
}

bool trial_prime(u32 x) {
    if (x < 2) return false;
    for (u32 d = 2; u64(d) * d <= x; ++d)
        if (x % d == 0) return false;
    return true;
}
u64 independent_transform(u32 x) {
    if ((x & 1U) && trial_prime(x)) return u64(2) * x;
    if (x % 3 == 0 && ((x / 3) & 1U) && trial_prime(x / 3))
        return u64(2) * (x / 3);
    return x;
}

u64 parse_integer(const char* text) {
    const std::string s(text);
    if (s.empty() || s.find_first_not_of("0123456789") != std::string::npos)
        throw std::runtime_error("expected an unsigned decimal integer");
    return std::stoull(s);
}
std::string hex64(u64 value) {
    std::ostringstream s;
    s << std::hex << std::setfill('0') << std::setw(16) << value;
    return s.str();
}
void digest_term(u64& hash, u32 value) {
    // FNV-1a over each term as exactly four little-endian bytes.
    for (unsigned shift = 0; shift < 32; shift += 8) {
        hash ^= (value >> shift) & 255U;
        hash *= 1099511628211ULL;
    }
}

int main(int argc, char** argv) {
    try {
        if (argc != 5)
            throw std::runtime_error("usage: ./ekg-table N CAPACITY CSV SUMMARY_JSON");
        const u64 count = parse_integer(argv[1]);
        const u64 capacity = parse_integer(argv[2]);
        if (count < 4096 || count > capacity || capacity > 1000000000ULL)
            throw std::runtime_error("require 4096 <= N <= CAPACITY <= 1000000000");
        // The capacity cap makes all cursor arithmetic fit in uint32_t and
        // every stored composite smallest factor fit in uint16_t.
        Generator gen{u32(capacity)};
        std::vector<u64> checkpoints;
        for (u64 power = 1000; power <= count; power *= 10) {
            for (u64 multiplier : {1ULL, 2ULL, 5ULL})
                if (power * multiplier <= count) checkpoints.push_back(power * multiplier);
        }
        checkpoints.push_back(count);
        std::sort(checkpoints.begin(), checkpoints.end());
        checkpoints.erase(std::unique(checkpoints.begin(), checkpoints.end()), checkpoints.end());
        std::ofstream csv(argv[3]);
        if (!csv) throw std::runtime_error("cannot open CSV");
        csv << "n,a,b,ratio,one_third,ratio_minus_one_third\n" << std::setprecision(18);
        std::vector<u32> prefix;
        prefix.reserve(4096);
        u32 value = 0, maximum = 0;
        u64 sum = 0, hash = 14695981039346656037ULL, prefix_hash = 0;
        u64 prime_replacements = 0, triple_replacements = 0;
        std::size_t checkpoint_index = 0, mutation_rejection = 0;
        u32 mutation_original = 0, mutation_value = 0;
        long double final_ratio = 0;
        for (u64 n = 1; n <= count; ++n) {
            if (n <= 2) { value = u32(n); gen.mark(value); }
            else value = gen.next(value);
            maximum = std::max(maximum, value);
            sum += value;
            digest_term(hash, value);
            const u64 b = gen.transform(value);
            if (b != value) {
                if (b == u64(2) * value) ++prime_replacements;
                else ++triple_replacements;
            }
            if (n <= 4096) {
                prefix.push_back(value);
                if (b != independent_transform(value))
                    throw std::runtime_error("independent transform check failed");
            }
            if (n == 4096) {
                prefix_hash = hash;
                if (naive_mismatch(prefix) != 0)
                    throw std::runtime_error("independent prefix check failed");
                auto mutated = prefix;
                constexpr std::size_t index = 128;
                mutation_original = mutated[index];
                std::set<u32> earlier(mutated.begin(), mutated.begin() + index);
                mutation_value = mutation_original + 1;
                while (earlier.count(mutation_value) ||
                       std::gcd(mutation_value, mutated[index - 1]) == 1)
                    ++mutation_value;
                mutated[index] = mutation_value;
                mutation_rejection = naive_mismatch(mutated);
                if (mutation_rejection != index + 1)
                    throw std::runtime_error("deliberate mutation was not rejected correctly");
                if (gen.transform(2) != 2 || gen.transform(6) != 6 ||
                    gen.transform(3) != 6 || gen.transform(9) != 6)
                    throw std::runtime_error("transform exception check failed");
            }
            if (checkpoint_index < checkpoints.size() && n == checkpoints[checkpoint_index]) {
                // Subtract exactly in signed integers, then evaluate the logarithm.
                const std::int64_t difference = std::int64_t(b) - std::int64_t(n);
                const long double ratio = static_cast<long double>(difference) *
                    std::log(static_cast<long double>(n)) / static_cast<long double>(n);
                const long double third = 1.0L / 3.0L;
                csv << n << ',' << value << ',' << b << ',' << ratio << ',' << third
                    << ',' << ratio - third << '\n';
                csv.flush();
                if (!csv) throw std::runtime_error("CSV write failed");
                final_ratio = ratio;
                ++checkpoint_index;
                if (n >= 1000000)
                    std::cerr << "checkpoint " << n << " a=" << value << " b=" << b << '\n';
            }
        }
        csv.close();
        if (!csv) throw std::runtime_error("CSV close failed");
        std::ofstream summary(argv[4]);
        if (!summary) throw std::runtime_error("cannot open summary");
        summary << std::setprecision(18)
            << "{\n  \"definition\": \"a(1)=1; a(2)=2; then least unused positive m with gcd(m,previous)>1\",\n"
            << "  \"b_definition\": \"Replace p and 3p by 2p for odd prime p only; 2 and 6 unchanged\",\n"
            << "  \"interpretation\": \"Numerical evidence only; no mathematical proof of a limiting value\",\n"
            << "  \"algorithm\": \"Odd composite uint16 smallest-prime-factor sieve; lazy least-unused-multiple cursor per prime; used bitmap; minimum over distinct prime divisors of previous term\",\n"
            << "  \"correctness_invariant\": \"Each prime cursor starts at p and skips only used multiples; all admissible integers are multiples of prime factors of previous; their minimum is the next term\",\n"
            << "  \"capacity_policy\": \"Every outside-capacity value is unused; cursors may cross the bound, but selection outside the bound aborts rather than truncating the candidate search\",\n"
            << "  \"constraints\": \"4096 <= N <= CAPACITY <= 1000000000; no full sequence stored; real output may differ in its last digits across math libraries\",\n"
            << "  \"compile_invocation\": \"g++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -o ekg-table ekg-table.cpp\",\n"
            << "  \"execution_invocation\": \"./ekg-table " << count << ' ' << capacity << " ekg-table.csv ekg-table-summary.json\",\n"
            << "  \"execution_arguments\": [" << count << ',' << capacity << "],\n"
            << "  \"execution_template\": \"./ekg-table N CAPACITY ekg-table.csv ekg-table-summary.json\",\n"
            << "  \"n\": " << count << ",\n  \"capacity\": " << capacity
            << ",\n  \"last_a\": " << value << ",\n  \"last_b\": " << gen.transform(value)
            << ",\n  \"last_ratio\": " << final_ratio
            << ",\n  \"ratio_definition\": \"(b(n)-n)*natural_log(n)/n; signed integer subtraction before long double evaluation; 18 significant output digits\""
            << ",\n  \"maximum_a\": " << maximum << ",\n  \"sum_a\": " << sum
            << ",\n  \"odd_prime_replacements\": " << prime_replacements
            << ",\n  \"triple_odd_prime_replacements\": " << triple_replacements
            << ",\n  \"digest_encoding\": \"FNV-1a-64; each a(n) encoded as four little-endian bytes; overflow modulo 2^64\",\n"
            << "  \"sequence_digest\": \"" << hex64(hash) << "\",\n"
            << "  \"prefix_digest\": \"" << hex64(prefix_hash) << "\",\n"
            << "  \"independent_prefix_terms_checked\": 4096,\n"
            << "  \"independent_transform_terms_checked\": 4096,\n"
            << "  \"prefix_validation_passed\": true,\n"
            << "  \"deliberate_mutation\": {\"index\":129,\"original\":" << mutation_original
            << ",\"replacement\":" << mutation_value << ",\"rejected_at\":" << mutation_rejection
            << ",\"preserves_unused_and_previous_gcd\":true},\n"
            << "  \"first_64_terms\": [";
        for (std::size_t i = 0; i < 64; ++i) summary << (i ? "," : "") << prefix[i];
        summary << "],\n  \"table_rows\": " << checkpoints.size()
            << "\n}\n";
        summary.close();
        if (!summary) throw std::runtime_error("summary write failed");
        return 0;
    } catch (const std::exception& e) {
        std::cerr << "error: " << e.what() << '\n';
        return 1;
    }
}
