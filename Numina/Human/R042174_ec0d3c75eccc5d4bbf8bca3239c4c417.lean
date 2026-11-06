import Mathlib

open Polynomial

/- Let $P(x)$ be a polynomial such that when $P(x)$ is divided by $x-17$, the remainder is $14$, and when $P(x)$ is divided by $x-13$, the remainder is $6$. What is the remainder when $P(x)$ is divided by $(x-13)(x-17)$? -/
theorem algebra_10778 {P : Polynomial ℝ} (hP1 : P.eval 17 = 14) (hP2 : P.eval 13 = 6) :
    P % ((X - C 13) * (X - C 17)) = C 2 * X - C 20 := by
  have custom_natDegree_mod_lt (p : ℝ[X]) {q : ℝ[X]} (hq : q.natDegree ≠ 0) :
    (p % q).natDegree < q.natDegree := by
    have hq' : q.leadingCoeff ≠ 0 := by
      rw [leadingCoeff_ne_zero]
      contrapose! hq
      simp [hq]
    rw [mod_def]
    refine (natDegree_modByMonic_lt p ?_ ?_).trans_le ?_
    · refine monic_mul_C_of_leadingCoeff_mul_eq_one ?_
      rw [mul_inv_eq_one₀ hq']
    · contrapose! hq
      rw [← natDegree_mul_C_eq_of_mul_eq_one ((inv_mul_eq_one₀ hq').mpr rfl)]
      simp [hq]
    · exact natDegree_mul_C_le q q.leadingCoeff⁻¹
  -- Let R be the remainder of P divided by ((X - C 13) * (X - C 17)).
  let R : Polynomial ℝ := P % ((X - C 13) * (X - C 17))
  rw [show P % ((X - C 13) * (X - C 17)) = R by dsimp]
  -- The degree of R is less than 2.
  have h₀ : natDegree R < 2 := by
    calc
      natDegree R < natDegree ((X - C 13) * (X - C 17) : Polynomial ℝ) := by apply custom_natDegree_mod_lt; rw [show ((X - C 13) * (X - C 17) : Polynomial ℝ).natDegree = 2 by compute_degree!]; norm_num
      _ = 2 := by compute_degree!
  replace h₀ : natDegree R ≤ 1 := by
    omega
  apply exists_eq_X_add_C_of_natDegree_le_one at h₀
  -- R(x) = ax + b.
  obtain ⟨a, b, h₀⟩ := h₀
  have h₁ := h₀
  rw [show R = P % ((X - C 13) * (X - C 17)) by dsimp] at h₁
  rw [<-modByMonic_eq_mod, modByMonic_eq_sub_mul_div] at h₁
  -- We have 14 = a * 17 + b.
  have h₂ : 14 = a * 17 + b := by
    calc
      14 = 14 - 0 := by norm_num
      _ = eval 17 P - eval 17 ((X - C 13) * (X - C 17) * (P /ₘ ((X - C 13) * (X - C 17)))) := by rw [hP1]; nth_rewrite 2 [mul_comm]; rw [mul_assoc, mul_comm, eval_mul_X_sub_C]
      _ = eval 17 (P - ((X - C 13) * (X - C 17) * (P /ₘ ((X - C 13) * (X - C 17))))) := by rw [eval_sub]
      _ = eval 17 (C a * X + C b) := by rw [h₁]
      _ = eval 17 (C a) * eval 17 (X) + eval 17 (C b) := by rw [eval_add, eval_mul]
      _ = a * 17 + b := by simp
  -- We have 6 = a * 13 + b.
  have h₃ : 6 = a * 13 + b := by
    calc
      6 = 6 - 0 := by norm_num
      _ = eval 13 P - eval 13 ((X - C 13) * (X - C 17) * (P /ₘ ((X - C 13) * (X - C 17)))) := by rw [hP2]; rw [mul_assoc, mul_comm, eval_mul_X_sub_C]
      _ = eval 13 (P - ((X - C 13) * (X - C 17) * (P /ₘ ((X - C 13) * (X - C 17))))) := by rw [eval_sub]
      _ = eval 13 (C a * X + C b) := by rw [h₁]
      _ = eval 13 (C a) * eval 13 (X) + eval 13 (C b) := by rw [eval_add, eval_mul]
      _ = a * 13 + b := by simp
  -- We have a = 2 and b = -20.
  have h₄ : a = 2 := by
    linarith only [h₂, h₃]
  have h₅ : b = -20 := by
    linarith only [h₂, h₃]
  rw [h₄, h₅, C_neg, Mathlib.Tactic.RingNF.add_neg] at h₀
  -- Solve remaining goals.
  exact h₀
  apply Monic.mul
  pick_goal 3
  apply Monic.mul
  all_goals
    rw [Monic.def]
    apply leadingCoeff_X_sub_C
