import Mathlib

set_option maxHeartbeats 400000
/-let a,b,c be positive real numbers such that a+b+c=10 and 
ab+bc+ca=25. let m = min {ab,bc,ca}. Find the largest possible value of m-/
theorem algebra_609358: IsGreatest {m: ℝ | ∃ a b c: ℝ, 0 < a ∧ a ≤ b ∧ b ≤ c ∧ a + b + c = 10 
∧ a * b + b * c + c * a = 25 ∧ m = min (min (a * b) (b * c)) (c * a)} (25 / 9) := by
  constructor
  
  -- the forward direction
  . simp
    use (5: ℝ) /3
    simp
    use (5: ℝ) /3
    simp
    use (20: ℝ) /3
    constructor
    . linarith
    . constructor
      . field_simp
        ring_nf
      . constructor
        . field_simp
          ring_nf
        . field_simp
          ring_nf
          norm_num

  -- the backward direction
  . intro m
    intro h
    simp at h
    obtain ⟨a, ha, b, hab,c,hbc, h1, h2,hm⟩ := h
    replace hm: m = a * b := by  -- first simplify the min function
      rw [hm]
      have eq1: min (a * b) (b * c) = a * b := by
        simp
        nlinarith
      rw [eq1]
      simp
      nlinarith
    have eq: (a - b) ^ 2 = (10 - c) ^ 2 - 4 * (25 - c * (10 - c)) := by
      calc
        (a - b) ^ 2 = (a + b) ^ 2 - 4 * a * b := by ring
                  _ = (10 - c) ^ 2 - 4 * (25 - c * (a + b)) := by nlinarith
                  _ = (10 - c) ^ 2 - 4 * (25 - c * (10 - c)) := by nlinarith
    have ineq: 0 ≤ (10 - c) ^ 2 - 4 * (25 - c * (10 - c)) := by
      rw [← eq]
      nlinarith
    have c_u: c ≤ (20: ℝ) / 3 := by nlinarith
    have c_l: (10: ℝ) / 3 ≤ c := by nlinarith
    have eq2: a * b = (c - 5) ^ 2 := by nlinarith
    rw [← hm] at eq2
    clear *- eq2 c_u c_l
    set s:= c - 5 with hs
    have s_u: s ≤ (5: ℝ) / 3 := by nlinarith
    have s_l: (-5: ℝ) / 3 ≤ s := by nlinarith
    clear c_l c_u
    rw [eq2]
    nlinarith