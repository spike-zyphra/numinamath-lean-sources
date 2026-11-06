import Mathlib

/- What is the positive difference of the solutions of $\dfrac{r^2-3r-17}{r+4}=2r+7$? -/
theorem algebra_14287 (r1 r2 : ℝ) (hr1 : (r1^2 - 3 * r1 - 17) / (r1 + 4) = 2 * r1 + 7)
    (hr2 : (r2^2 - 3 * r2 - 17) / (r2 + 4) = 2 * r2 + 7) (hr : r1 ≠ r2) :
    abs (r1 - r2) = 12 := by
  -- for (r^2-3r-17)/(r+4) = 2r+7, multiply both sides (r+4) to get a nice form.
  have h1: ∀r:ℝ, r ≠ -4 → (r^2-3*r-17)/(r+4) = 2*r+7 → r^2-3*r-17 = (2*r+7) * (r+4) := by
    intro r nez' heq
    have: r^2-3*r-17 = (r^2-3*r-17)/(r+4) * (r+4) := by
      have nez: r+4 ≠ 0 := by
        by_contra! hc
        have: r = -4 := by linarith [hc]
        rw [this] at nez'
        norm_num at nez'
      field_simp [nez]
    rw [this, heq]
  -- now we have (r^2-3r-17)=(2r+7)(r+4). since (2r+7)(r+4)=2r^2+15r+28, after some calculation, the equation can be simplified to r^2+18r+45=0
  have h2: ∀r:ℝ, r^2-3*r-17=(2*r+7)*(r+4) → r^2+18*r+45=0 := by
    intro r eq1
    have: (2*r+7)*(r+4) = 2*r^2+15*r+28 := by ring
    rw [this] at eq1
    have eq2: 0 = (2*r^2+15*r+28)-(r^2-3*r-17) := by
      rw [eq1]; simp
    rw [eq2]; ring
  -- factorization, r^2+18r+45 = (r+3)(r+15), therefore r = -3 or -15
  have h3: ∀r:ℝ, r^2+18*r+45=0 → (r=-3 ∨ r=-15) := by
    intro r eq
    have: r^2+18*r+45 = (r+3)*(r+15) := by ring
    rw [this] at eq
    have req': r+3 = 0 ∨ r+15 = 0 := mul_eq_zero.mp eq
    rcases req' with eqn3' | eqn15'
    left; linarith [eqn3']
    right; linarith [eqn15']
  -- therefore, r1,r2 one is -3 and the other -15. positive difference is 12.
  -- first r1.
  have r1eq: r1 = -3 ∨ r1 = -15 := by
    by_cases r1n4: r1 = -4
    rw [r1n4] at hr1; simp at hr1; norm_num at hr1
    push_neg at r1n4
    -- now r1 ≠ 4
    have h1': r1^2-3*r1-17 = (2*r1+7)*(r1+4) := h1 r1 r1n4 hr1
    have h2': r1^2+18*r1+45 = 0 := h2 r1 h1'
    apply h3 r1 h2'
  -- next, same operation to r2.
  have r2eq: r2 = -3 ∨ r2 = -15 := by
    by_cases r2n4: r2 = -4
    rw [r2n4] at hr2; simp at hr2; norm_num at hr2
    push_neg at r2n4
    -- now r2 ≠ 4
    have h1': r2^2-3*r2-17 = (2*r2+7)*(r2+4) := h1 r2 r2n4 hr2
    have h2': r2^2+18*r2+45 = 0 := h2 r2 h1'
    apply h3 r2 h2'
  -- r1=-3 or -15, r2=-3 or -15. four cases in total. r1≠r2, so |r1-r2|=12.
  rcases r1eq with r1n3 | r1n15
  rcases r2eq with r2n3 | r2n15
  rw [r1n3,r2n3] at hr; norm_num at hr
  rw [r1n3,r2n15]; norm_num
  rcases r2eq with r2n3 | r2n15
  rw [r1n15,r2n3]; norm_num
  rw [r1n15,r2n15] at hr; norm_num at hr