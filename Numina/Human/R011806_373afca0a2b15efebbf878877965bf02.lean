import  Mathlib

/-
Points $A, B, C$, and $D$ lie on a line in that order such that $\frac{A B}{B C}=\frac{D A}{C D}$. If $A C=3$ and $B D=4$, find $A D$.
-/

theorem algebra_609739  (A B C D : ℝ) (h₀ : A < B ∧ B < C ∧ C < D)  (h₁ : (B - A) / (C - B) = (D - A) / (D - C)) (h₂ : C - A = 3) (h₃ : D - B = 4) : D - A = 6 := by
  
  -- Rewrite the C-B = x and simplifying h₁
  let x:ℝ := C - B
  have _1: B - A = 3 - x := by rw [← h₂]; ring
  have _2: C - B = x := by linarith
  have _3: D - A = 7 - x := by
    rw [show D = 4 + B by linarith]; unfold x;
    rw [show C = 3 + A by linarith]; ring_nf;
  have _4: D - C = 4 - x := by
    unfold x; rw [show D = 4 + B by linarith]; ring_nf
  have : D - C > 0 := by linarith
  have : C - B > 0 := by linarith
  field_simp at h₁
  rw [_1, _2, _3, _4] at h₁
  
  -- Solve for x from the eqaution given in h₁
  have h1: x^2 - 7*x + 12 = 7*x - x^2 := by linarith
  have : 2*x^2 - 14*x + 12 = 0 := by linarith
  have hend: (x - 1)*(x - 6) = 0 := by linarith

  -- We know that x ≠ 6 because it will contradict with the assumption. Therefore, x = 1.
  have : x < 3 := by
    have : 3 - x > 0 := by linarith
    linarith
  have : (x - 6) ≠ 0 := by linarith
  have : x - 1 = 0 := by
    calc
      _ = (x-1)*(x-6)/(x-6) := by field_simp
      _ = 0 / (x - 6):= by rw[hend]
      _ = _ := by norm_num
  have : x = 1 := by linarith
  have : D - A = 7 - x := _3
  linarith
  

    