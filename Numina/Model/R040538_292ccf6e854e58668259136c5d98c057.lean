import Mathlib

theorem algebra_280440 {f : ℝ → ℝ} (hf : ∀ x, f x + x * f (2 - x) = 2) :
    f = fun x => if x ≠ 1 then 2 / (1 - x) else 1 := by
  funext x
  by_cases h : x ≠ 1
  · -- Assume x ≠ 1
    have eq1 := hf x
    have eq2 := hf (2 - x)
    have eq2x : 2 - (2 - x) = x := by ring
    have eq2' : f (2 - x) + (2 - x) * f x = 2 := by
      simp [eq2x] at eq2 ⊢
      linarith [eq2]
    have eq3 : f x = 2 / (1 - x) := by
      have eq5 : f (2 - x) = 2 - (2 - x) * f x := by linarith [eq2']
      rw [eq5] at eq1
      have eq7 : f x * (1 - x) ^ 2 = 2 * (1 - x) := by
        nlinarith
      have hx1 : (1 - x) ≠ 0 := by
        intro h1
        apply h
        linarith
      have eq8 : f x * (1 - x) = 2 := by
        apply (mul_left_inj' hx1).mp
        linarith
      have hx2 : (1 - x) ≠ 0 := hx1
      field_simp [hx2] at eq8 ⊢
      nlinarith
    rw [if_pos h]
    exact eq3
  · -- Assume x = 1
    have h1 : x = 1 := by
      by_contra h1
      push_neg at h1
      tauto
    have eq1 := hf 1
    have eq2 : f 1 = 1 := by
      norm_num [h1] at eq1 ⊢
      linarith
    rw [if_neg (by tauto)]
    simp [eq2, h1]