import Mathlib

open Real

/- (Inequality of the bad students)

Let $a_{1}, \ldots, a_{n}$ and $b_{1}, \ldots, b_{n}$ be positive non-zero real numbers. Show that we have $\frac{a_{1}^{2}}{b_{1}}+\ldots+\frac{a_{n}^{2}}{b_{n}} \geqslant$ $\frac{\left(a_{1}+\ldots+a_{n}\right)^{2}}{b_{1}+\ldots+b_{n}}$ -/
theorem inequalities_127664 {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
    ∑ i, (a i)^2 / b i ≥ (∑ i, a i)^2 / ∑ i, b i := by
  -- first let's prove the sums are positive, as this'll be useful later
  have h_sum_pos₁ : 0 < ∑ i, (a i)^2 / b i := by
    apply Finset.sum_pos
    . simp; rintro i
      simp [hb i, ha i]
    . use ⟨0, by linarith⟩; simp
  have h_sum_pos₂ : 0 < ∑ i, b i := by
    apply Finset.sum_pos
    . simp; exact hb
    . use ⟨0, by linarith⟩; simp
  have h_sum_pos₃ : 0 < ∑ i, a i := by
    apply Finset.sum_pos
    . simp; exact ha
    . use ⟨0, by linarith⟩; simp
  -- next convert the goal to multiplication format instead of division format
  suffices (∑ i, a i)^2 ≤ (∑ i, (a i)^2 / b i) * (∑ i, b i) by
    calc
      (∑ i, a i)^2 / ∑ i, b i ≤ (∑ i, (a i)^2 / b i) * (∑ i, b i) / ∑ i, b i := by gcongr
      _ = (∑ i, (a i)^2 / b i) := by field_simp
  -- define two n-dimensional euclidean vector which will allow us to use cauchy schwearz inequality
  let a' : EuclideanSpace ℝ <| Fin n := fun i => a i / √ (b i)
  let b' : EuclideanSpace ℝ <| Fin n := fun i => √ (b i)
  have hcs := real_inner_le_norm a' b'
  -- show that ‖a'‖ is square root of one of the sums
  have : ‖a'‖ = √(∑ i, (a i)^2 / b i) := by
    simp [PiLp.norm_eq_of_L2]
    congr; ext i
    simp [a']
    rw [div_pow, Real.sq_sqrt]
    linarith [hb i]
  rw [this] at hcs
  -- show that ‖b'‖ is square root of one of the sums
  have : ‖b'‖ = √(∑ i, b i) := by
    simp [PiLp.norm_eq_of_L2]
    congr; ext i
    simp [b']
    rw [Real.sq_sqrt]
    linarith [hb i]
  rw [this] at hcs
  -- show that inner a' b' is one of the sums
  have : inner a' b' = ∑ i, a i := by
    simp
    congr; ext i
    simp [a', b']
    have : √(b i) > 0 := Real.sqrt_pos.mpr <| hb i
    field_simp
  rw [this] at hcs
  -- finally square the inequality and simplify to get the goal
  replace hcs := sq_le_sq₀ (by positivity) (by positivity) |>.mpr hcs
  rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)] at hcs
  exact hcs