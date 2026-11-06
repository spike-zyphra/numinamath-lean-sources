import Mathlib

theorem algebra_245001 {x y : ℝ} (h : x ≠ 0) (h' : y ≠ 0)
    (h1 : ∃ k, x = k * y) :
    ∃ m, 1 / x = m * 1 / y := by
  rcases h1 with ⟨k, hk⟩
  use 1 / k
  have hkne0 : k ≠ 0 := by
    by_contra hkz
    have hx : x = 0 := by 
      rw [hkz] at hk
      simp [h'] at hk 
      linarith 
    contradiction
  field_simp [hk, h, h', hkne0]
  <;> linarith