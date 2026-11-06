import Mathlib

theorem algebra_128384 (a b c : ℝ) (h : a ≠ 0) (h' : b ≠ 0) (h'' : c ≠ 0)
    (h''' : ∃ r, b = a * r ∧ c = b * r) :
    a = 3 ∧ b = 5 ∧ c = 9 → False := by 
  intro h1
  rcases h''' with ⟨r, h2, h3⟩
  rcases h1 with ⟨ha, hb, hc⟩
  rw [ha] at h2
  rw [hb] at h2
  rw [hb] at h3
  rw [hc] at h3
  have hr : r = 5 / 3 := by
    linarith
  rw [hr] at h3
  linarith