import Mathlib

theorem algebra_137934 {k : ℝ} (h : ∃ x y, x ≠ y ∧ 2*x^2+k*x-2*k+1=0 ∧ 2*y^2+k*y-2*k+1=0 ∧ x^2+y^2=29/4) :
    k=3 := by
  rcases h with ⟨x, y, hxy, hx, hy, h1⟩
  have h2 : 2*(x^2 - y^2) + k*(x - y) = 0 := by
    nlinarith
  have h3 : (x - y) * (2*(x + y) + k) = 0 := by
    ring_nf at h2 ⊢
    linarith
  cases' (mul_eq_zero.mp h3) with h4 h5
  · -- We have $x - y = 0$, which contradicts to $x \neq y$
    exfalso
    apply hxy
    linarith 
  · -- We have $2(x + y) + k = 0$
    have hk : k = -2 * (x + y) := by linarith
    have h1' : x^2 + y^2 = 29/4 := by linarith
    have h3' : -2 * x * y + 4 * (x + y) + 1 = 0 := by 
      rw [hk] at hx hy
      nlinarith 
    have h5_s : (x + y) = -3/2 := by 
      nlinarith [sq_pos_of_ne_zero (show x - y ≠ 0 by 
        intro h0 
        apply hxy 
        linarith 
      ), sq_nonneg (x - y)]
    have hk3 : k = 3 := by
      nlinarith [h5_s, sq_nonneg (x - y)]
    linarith