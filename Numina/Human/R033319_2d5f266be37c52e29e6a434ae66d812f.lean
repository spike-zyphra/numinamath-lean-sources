import Mathlib


open Finset Polynomial


/- The real numbers $x_{1}, x_{2}, \ldots, x_{1996}$ have the following property: for any polynomial $W$ of degree 2 at least three of the numbers $W\left(x_{1}\right), W\left(x_{2}\right), \ldots, W\left(x_{1996}\right)$ are equal. Prove that at least three of the numbers $x_{1}, x_{2}, \ldots, x_{1996}$ are equal.-/
theorem algebra_239069 (x : ℕ → ℝ)
    (h : ∀ W : Polynomial ℝ, W.degree = 2 →
      ∃ a b c, (a < 1996 ∧ b < 1996 ∧ c  < 1996 ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
        W.eval (x a) = W.eval (x b) ∧
        W.eval (x b) = W.eval (x c) ∧
        W.eval (x c) = W.eval (x a))) :
    ∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
    x a = x b ∧ x b = x c := by
  have nonempty_aux : (Finset.range 1996).Nonempty := by
    simp
  have fin_image : (image x (range 1996)).Nonempty := by
    simp
  let m := Finset.min' (image x (range 1996)) fin_image
  let W : Polynomial ℝ := (X - C m) ^ 2
  have degW : W.degree = 2 := by 
    unfold W
    simp
  obtain ⟨a,b,c, h⟩ := h W degW
  obtain ⟨ha,hb,hc, hab, hac, hbc, hwab, hwbc, hwac⟩ := h
  have minle : ∀ (i : ℕ), i < 1996 → x i ≥ m := by
    intro i hi
    have i_in : i ∈ range 1996 := by
      simpa
    apply Finset.min'_le
    simp
    use i
    -- W (xi) = W (x j) → x i = x j
  have W_inj : ∀ (i j : ℕ ), ((i < 1996) ∧ (j < 1996)) →  W.eval (x i) = W.eval (x j) → x i = x j := by 
    intro i j ⟨hi, hj⟩ heval
    unfold W at heval
    simp at heval
    obtain minlei := minle i hi
    obtain minlej := minle j hj
    have pos : x i - m ≥ 0 := by linarith
    have pos' : x j - m ≥ 0 := by linarith
    have eq_aux : x i - m = x j - m := (sq_eq_sq₀ pos pos').mp heval
    calc 
      _ = x i - m + m := by ring
      _ = x j := by rw [eq_aux];ring
  
  obtain hw1 := W_inj a b ⟨ha, hb⟩ hwab
  obtain hw2 := W_inj b c ⟨hb, hc⟩ hwbc
  obtain hw3 := W_inj c a ⟨hc, ha⟩ hwac
  use a
  use b
  use c
  
