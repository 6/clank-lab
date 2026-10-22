import Generated.Tail
import Generated.Direct6
import Generated.Direct15
import Generated.Width4
import Generated.Width5
import Generated.Width6
import Generated.Width7
import Generated.Width8
import Generated.Width9
import Generated.Width10
import Generated.Width11
import Generated.Width12
import Generated.Width13
import Generated.Width14
import Generated.Width15
import Generated.Width16
import Generated.Width17
import Generated.Width18
import Generated.Width19
import Generated.Width20
import Generated.Width21
import Generated.Width22
import Generated.Width23
import Generated.Width24
import Generated.Width25
import Generated.Width26
import Generated.Width27
import Generated.Width28
import Generated.Width29
import Generated.Width30
import Generated.Width31
import Generated.Width32
import Generated.Width33
import Generated.Width34
import Generated.Width35
import Generated.Width36
import Generated.Width37
import Generated.Width38
import Generated.Width39
import Generated.Width40
import Generated.Width41
import Generated.Width42
import Generated.Width43
import Generated.Width44
import Generated.Width45
import Generated.Width46
import Generated.Width47
import Generated.Width48
import Generated.Width49
import Generated.Width50
import Generated.Width51
import Generated.Width52
import Generated.Width53
import Generated.Width54
import Generated.Width55

namespace LockedTromino.Witnesses
def actualCertificate : ProposedCertificate where
  small := by
    intro w hlo hhi hne
    by_cases h4 : w = 4
    · subst w; exact Width4_palette
    by_cases h6 : w = 6
    · subst w; exact Width6_palette
    by_cases h7 : w = 7
    · subst w; exact Width7_palette
    by_cases h8 : w = 8
    · subst w; exact Width8_palette
    by_cases h9 : w = 9
    · subst w; exact Width9_palette
    by_cases h10 : w = 10
    · subst w; exact Width10_palette
    by_cases h11 : w = 11
    · subst w; exact Width11_palette
    by_cases h12 : w = 12
    · subst w; exact Width12_palette
    by_cases h13 : w = 13
    · subst w; exact Width13_palette
    by_cases h14 : w = 14
    · subst w; exact Width14_palette
    by_cases h15 : w = 15
    · subst w; exact Width15_palette
    by_cases h16 : w = 16
    · subst w; exact Width16_palette
    by_cases h17 : w = 17
    · subst w; exact Width17_palette
    by_cases h18 : w = 18
    · subst w; exact Width18_palette
    by_cases h19 : w = 19
    · subst w; exact Width19_palette
    by_cases h20 : w = 20
    · subst w; exact Width20_palette
    by_cases h21 : w = 21
    · subst w; exact Width21_palette
    by_cases h22 : w = 22
    · subst w; exact Width22_palette
    by_cases h23 : w = 23
    · subst w; exact Width23_palette
    by_cases h24 : w = 24
    · subst w; exact Width24_palette
    by_cases h25 : w = 25
    · subst w; exact Width25_palette
    by_cases h26 : w = 26
    · subst w; exact Width26_palette
    by_cases h27 : w = 27
    · subst w; exact Width27_palette
    by_cases h28 : w = 28
    · subst w; exact Width28_palette
    by_cases h29 : w = 29
    · subst w; exact Width29_palette
    by_cases h30 : w = 30
    · subst w; exact Width30_palette
    by_cases h31 : w = 31
    · subst w; exact Width31_palette
    by_cases h32 : w = 32
    · subst w; exact Width32_palette
    by_cases h33 : w = 33
    · subst w; exact Width33_palette
    by_cases h34 : w = 34
    · subst w; exact Width34_palette
    by_cases h35 : w = 35
    · subst w; exact Width35_palette
    by_cases h36 : w = 36
    · subst w; exact Width36_palette
    by_cases h37 : w = 37
    · subst w; exact Width37_palette
    by_cases h38 : w = 38
    · subst w; exact Width38_palette
    by_cases h39 : w = 39
    · subst w; exact Width39_palette
    by_cases h40 : w = 40
    · subst w; exact Width40_palette
    by_cases h41 : w = 41
    · subst w; exact Width41_palette
    by_cases h42 : w = 42
    · subst w; exact Width42_palette
    by_cases h43 : w = 43
    · subst w; exact Width43_palette
    by_cases h44 : w = 44
    · subst w; exact Width44_palette
    by_cases h45 : w = 45
    · subst w; exact Width45_palette
    by_cases h46 : w = 46
    · subst w; exact Width46_palette
    by_cases h47 : w = 47
    · subst w; exact Width47_palette
    by_cases h48 : w = 48
    · subst w; exact Width48_palette
    by_cases h49 : w = 49
    · subst w; exact Width49_palette
    by_cases h50 : w = 50
    · subst w; exact Width50_palette
    by_cases h51 : w = 51
    · subst w; exact Width51_palette
    by_cases h52 : w = 52
    · subst w; exact Width52_palette
    by_cases h53 : w = 53
    · subst w; exact Width53_palette
    by_cases h54 : w = 54
    · subst w; exact Width54_palette
    by_cases h55 : w = 55
    · subst w; exact Width55_palette
    omega
  five := ⟨Direct6_b0, Direct15_b0, Width5_palette⟩
  tail := tailPalette

/-- Exact universal construction, with no finite-certificate hypotheses. -/
theorem locked_tromino_rectangles (m n : Nat) (hm : 6 ≤ m) (hd : 3 ∣ m) (hn : 4 ≤ n) :
    ∃ T, Locked (Rectangle m n) T :=
  universal_of_proposed_certificate actualCertificate m n hm hd hn

#print axioms locked_tromino_rectangles

end LockedTromino.Witnesses
