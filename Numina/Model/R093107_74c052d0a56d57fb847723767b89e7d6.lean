import Mathlib

open Real

theorem inequalities_8734
    (f : ℝ → ℝ)
    (h₀ : StrictMonoOn f (Set.Ioi 0))
    (h₁ : ∀ x y : ℝ, 0 < x → 0 < y → (f ((x + y) / 2) < (f x + f y) / 2)) :
    ¬∃ a d : ℝ, ∀ n : ℕ, f (n + 1) = a + d * n := by 
  intro ⟨a, d, hd⟩
  have h1 := h₁ 1 3 (by norm_num) (by norm_num)
  have ha1 := hd 0
  have ha2 := hd 1
  have ha3 := hd 2
  norm_num at ha1 ha2 ha3
  rw [show (1 + 3 : ℝ) / 2 = (2 : ℝ) by norm_num] at h1
  rw [show (f 1 + f 3) / 2 = f 2 by linarith [ha1, ha3]] at h1
  linarith [ha2, h1]