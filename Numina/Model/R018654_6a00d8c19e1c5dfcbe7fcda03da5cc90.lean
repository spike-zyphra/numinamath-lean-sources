import Mathlib

theorem algebra_204990 {x : ℕ} (hx : Even x) (h : x / 2 + 2 * (x - 1) = 40) :
    x = 46 := by
  have h1 : x % 2 = 0 := by
    obtain ⟨m, hm⟩ := hx
    omega
  have h3 : x ≤ 20 := by
    by_contra h4
    push_neg at h4
    have h5 : x / 2 + 2 * (x - 1) > 40 := by
      omega
    omega
  interval_cases x <;> norm_num at h h1 ⊢ <;> omega