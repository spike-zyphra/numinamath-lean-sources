import Mathlib
open Real
/-
Let $k$ be an integer and $n$ be a positive integer such that $n$ is not the square of any integer. Let $x$ be a real number defined by $x = \sqrt{k + \sqrt{n}}$. If $k + \sqrt{n} > 0$, prove that $x$ is irrational.
-/

theorem number_theory_636529 (k n : ℤ) (hn : 0 < n ∧ ¬ IsSquare n) (x:ℝ) (hx : x = sqrt (k + sqrt n)) (h: k + sqrt (n) > 0):
  Irrational x := by

  simp at hn h
  obtain ⟨npos,hn⟩ := hn

  --If it is rational, then we will prove that √n is rational.
  --which is a contradiction to that n is not a square.
  by_contra hr
  rw [irrational_iff_ne_rational] at hr
  push_neg at hr
  obtain ⟨a,b,hr⟩ := hr
  have bne0 : b ≠ 0 := by 
    by_contra be0
    simp [be0] at hr
    simp [hr] at hx
    have : (↑k + √↑n) ≤ 0 := by exact sqrt_eq_zero'.mp (id (Eq.symm hx))
    linarith
  have b2ne0 : b^2 ≠ 0 := by exact pow_ne_zero 2 bne0

  have eq1: x^2 = (↑k + √↑n) := by
    rw [hx]
    refine sq_sqrt ?_
    linarith
  
  have eq2 : √n = (a^2-k*b^2) / b^2 := by 
    have l : x^2 = a^2 / b^2 := by
      rw [hr]
      field_simp
    rw [eq1] at l
    have tmp : √↑n = ↑a ^ 2 / ↑b ^ 2 - k := by
      linarith
    rw [tmp]
    have tmp2 : ↑k = (↑k * ↑b ^ 2) / ↑b ^ 2 := by 
      field_simp
    nth_rw 1 [tmp2]
    field_simp
    ring

  have t: Irrational √n := by 
    rw [irrational_sqrt_intCast_iff_of_nonneg]
    exact hn
    linarith
  rw [irrational_iff_ne_rational] at t
  specialize t (a^2 - k*b^2) (b^2)
  simp [eq2] at t
  
  