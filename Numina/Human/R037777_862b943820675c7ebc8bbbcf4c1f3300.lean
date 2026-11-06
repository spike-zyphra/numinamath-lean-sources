import Mathlib

open Real

/-
Let $x_1, x_2, ... , x_6$ be non-negative real numbers such that $x_1 +x_2 +x_3 +x_4 +x_5 +x_6 =1$, and $x_1 x_3 x_5 +x_2 x_4 x_6 \ge {\frac{1}{540}}$. Let $p$ and $q$ be positive relatively prime integers such that $\frac{p}{q}$ is the maximum possible value of
$x_1 x_2 x_3 + x_2 x_3 x_4 +x_3 x_4 x_5 +x_4 x_5 x_6 +x_5 x_6 x_1 +x_6 x_1 x_2$. Find $p+q$.
-/

theorem inequalities_95040 :
IsGreatest {y | ∃ t : Fin 6 → ℝ,
(∀ i, 0 ≤ t i) ∧ (∑ i, t i = 1) ∧ t 0 * t 2 * t 4 + t 1 * t 3 * t 5 ≥ 1 / 540 ∧
y = t 0 * t 1 * t 2 + t 1 * t 2 * t 3 + t 2 * t 3 * t 4 + t 3 * t 4 * t 5 + t 4 * t 5 * t 0 + t 5 * t 0 * t 1} (19 / 540) := by
  rw [IsGreatest, upperBounds]
  constructor
  · dsimp
    -- Provide an explicit construction to achieve the claimed upper bound
    let t : Fin 6 → ℝ
    | ⟨0, _⟩ => 1/3
    | ⟨1, _⟩ => 19/60
    | ⟨2, _⟩ => 1/3
    | ⟨3, _⟩ => 0
    | ⟨4, _⟩ => 1/60
    | ⟨5, _⟩ => 0
    use t
    constructor
    -- Check nonnegativity conditions
    · intro i
      match i with
      | ⟨0, _⟩ => norm_num
      | ⟨1, _⟩ => norm_num
      | ⟨2, _⟩ => norm_num
      | ⟨3, _⟩ => norm_num
      | ⟨4, _⟩ => norm_num
      | ⟨5, _⟩ => norm_num
    constructor
    -- Check sum condition
    · repeat rw [Fin.sum_univ_succ]
      simp
      repeat rw [Fin.succ]
      simp
      norm_num
    constructor
    -- Check inequality condition
    · norm_num
    -- Check it actually achieves the upper bound
    norm_num
  -- Now we prove 19/540 is actually an upper bound
  simp
  intro a x hx₁ hx₂ hx₃ ha
  repeat rw [Fin.sum_univ_succ] at hx₂
  simp at hx₂
  repeat rw [Fin.succ] at hx₂
  simp at hx₂
  rw [ha]
  -- Result of using AM-GM
  have amgm : (x 0 + x 3) * (x 1 + x 4) * (x 2 + x 5) ≤ (1 / 27 : ℝ) := by
    have p1' : 0 ≤ x 0 + x 3 := by linarith [hx₁ 0, hx₁ 3]
    have p2' : 0 ≤ x 1 + x 4 := by linarith [hx₁ 1, hx₁ 4]
    have p3' : 0 ≤ x 2 + x 5 := by linarith [hx₁ 2, hx₁ 5]
    have bound : (x 0 + x 3)^(1/3 : ℝ) * (x 1 + x 4)^(1/3 : ℝ) * (x 2 + x 5)^(1/3 : ℝ) ≤ (1/3 : ℝ) := by
      calc
      (x 0 + x 3)^(1/3 : ℝ) * (x 1 + x 4)^(1/3 : ℝ) * (x 2 + x 5)^(1/3 : ℝ) ≤ (1/3) * (x 0 + x 3) + (1/3) * (x 1 + x 4) + (1/3) * (x 2 + x 5) := by
        have : 0 ≤ (1/3 : ℝ) := by positivity
        have p4 : (1/3 : ℝ) + (1/3) + (1/3) = 1 := by norm_num
        apply geom_mean_le_arith_mean3_weighted this this this p1' p2' p3' p4
      _ = (1/3 : ℝ) := by linarith
    have p1 : 0 ≤ (x 0 + x 3) * (x 1 + x 4) * (x 2 + x 5) := by
      apply mul_nonneg
      apply mul_nonneg
      exact p1'
      exact p2'
      exact p3'
    have p2 : 0 ≤ (1/27 : ℝ) := by norm_num
    have p3 : 0 < (1/3 : ℝ) := by norm_num
    have p4 : 0 ≤ (1/3 : ℝ) := by norm_num
    have p5 : (3 : ℝ) ≠ 0 := by norm_num
    rw [← rpow_le_rpow_iff p1 p2 p3]
    rw [mul_rpow (mul_nonneg p1' p2') (by linarith), mul_rpow (by linarith)]
    swap; exact p2'
    have : (1/27 : ℝ) = (1/3) ^ (3 : ℝ) := by norm_num
    rw [this]
    nth_rw 5 [one_div]
    rw [rpow_rpow_inv (show 1/3 ≥ 0 by positivity) (show 3 ≠ 0 by positivity)]
    exact bound
  -- Plug in result of AM-GM to get bound
  calc
  x 0 * x 1 * x 2 + x 1 * x 2 * x 3 + x 2 * x 3 * x 4 + x 3 * x 4 * x 5 + x 4 * x 5 * x 0 + x 5 * x 0 * x 1 = x 0 * x 1 * x 2 + x 1 * x 2 * x 3 + x 2 * x 3 * x 4 + x 3 * x 4 * x 5 + x 4 * x 5 * x 0 + x 5 * x 0 * x 1 + x 0 * x 2 * x 4 + x 1 * x 3 * x 5 - (x 0 * x 2 * x 4 + x 1 * x 3 * x 5) := by simp
  _ = (x 0 + x 3) * (x 1 + x 4) * (x 2 + x 5) - (x 0 * x 2 * x 4 + x 1 * x 3 * x 5) := by ring
  _ ≤ 1/27 - 1/540 := by linarith
  _ = 19/540 := by norm_num