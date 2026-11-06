import Mathlib


open Real Nat Set


theorem number_theory_137128 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : Irrational (a / b)) (x : ℝ) (hx : x ∈ Set.Icc (-a) b) :
    ∃ n, |x + n * a| < 10 ^ (-6 : ℤ) := by
  rcases hx with ⟨h1, h2⟩
  have h3 : (10 : ℝ) ^ (-6 : ℤ) = (1 / 10 ^ 6 : ℝ) := by norm_num
  use (-x) / a 
  have ha' : a ≠ 0 := by linarith
  field_simp
  all_goals nlinarith