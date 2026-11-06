import Mathlib
open Real
noncomputable section

-- Prove the AM-GM inequality for two non-negative real numbers using geometric and arithmetic means.
lemma am_gm_ineq (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : sqrt (x * y) ≤ (x + y) / 2 := by
  -- Define the finite set and functions.
  let s : Finset (Fin 2) := {0, 1}
  let w : Fin 2 → ℝ := fun _ => 1
  let z : Fin 2 → ℝ := ![x, y]
  -- Verify conditions for geom_mean_le_arith_mean.
  have h_w_nonneg : ∀ i ∈ s, 0 ≤ w i := by
    intro i _
    simp [w]
  have h_w_sum_pos : 0 < ∑ i ∈  s, w i := by
    simp [w, s]
  have h_z_nonneg : ∀ i ∈ s, 0 ≤ z i := by
    intro i hi
    simp only [s, Set.mem_insert, Set.mem_singleton] at hi
    fin_cases hi <;> simp [z]
    · exact hx
    · exact hy
  -- Compute geometric and arithmetic means.
  have h_geom : (∏ i ∈  s, z i ^ w i) = x * y := by
    simp [w, z, s]
  have h_sum_w : ∑ i ∈  s, w i = 2 := by
    simp [w, s]
  have h_geom_mean : (∏ i ∈ s, z i ^ w i) ^ (∑ i ∈  s, w i)⁻¹ = sqrt (x * y) := by
    rw [h_geom, h_sum_w]
    simp [sqrt_eq_rpow]
  have h_arith_mean : (∑ i ∈ s, w i * z i) / ∑ i ∈  s, w i = (x + y) / 2 := by
    simp [w, z, s]
  -- Apply geom_mean_le_arith_mean.
  have h_am_gm : (∏ i ∈ s, z i ^ w i) ^ (∑ i ∈ s, w i)⁻¹ ≤ (∑ i ∈ s, w i * z i) / ∑ i ∈ s, w i :=
    geom_mean_le_arith_mean s w z h_w_nonneg h_w_sum_pos h_z_nonneg
  rw [h_geom_mean, h_arith_mean] at h_am_gm
  exact h_am_gm

/- Soit $a, b, c \geqslant 1$ des entiers tels que $a^{b} \mid b^{c}$ et $a^{c} \mid c^{b}$. Montrer que $a^{2} \mid b c$. -/
theorem number_theory_607379 (a b c : ℕ) (ha : 1 ≤ a) (h₀ : 1 ≤ b) (h₁ : 1 ≤ c)
    (h₂ : a ^ b ∣ b ^ c) (h₃ : a ^ c ∣ c ^ b) : a ^ 2 ∣ b * c := by 
  -- Express divisibility via p-adic valuations.
  have h_val : ∀ p, Prime p → 2 * multiplicity p a ≤ multiplicity p b + multiplicity p c := by
    intro p hp
    let v_a := multiplicity p a
    let v_b := multiplicity p b
    let v_c := multiplicity p c
    have hp' : Fact (Nat.Prime p) := by
      exact Fact.mk (Nat.prime_iff.mpr hp)
    have hp'' : Nat.Prime p := by
      exact Nat.prime_iff.mpr hp
    -- Ensure finite multiplicity for $p$ in $a, b, c$.
    have h_v_a : FiniteMultiplicity p a := by
      rw [Nat.finiteMultiplicity_iff]
      split_ands
      · exact Prime.ne_one hp
      · nlinarith
    have h_v_b : FiniteMultiplicity p b := by
      rw [Nat.finiteMultiplicity_iff]
      split_ands
      · exact Prime.ne_one hp
      · nlinarith
    have h_v_c : FiniteMultiplicity p c := by
      rw [Nat.finiteMultiplicity_iff]
      split_ands
      · exact Prime.ne_one hp
      · nlinarith
    -- Valuation inequalities $v_a * b ≤ v_b * c$ from divisibility.
    have h_val_1 : v_a * b ≤ v_b * c := by
      unfold v_a v_b
      have h_v_ab : FiniteMultiplicity p (a ^ b) := by
        rw [Nat.finiteMultiplicity_iff]
        split_ands
        · exact Prime.ne_one hp
        · have : 0 < a ^ b := pow_pos (by nlinarith) b
          exact this
      have h_v_bc : FiniteMultiplicity p (b ^ c) := by
        rw [Nat.finiteMultiplicity_iff]
        split_ands
        · exact Prime.ne_one hp
        · have : 0 < b ^ c := pow_pos (by nlinarith) c
          exact this
      have h_le : multiplicity p (a ^ b) ≤ multiplicity p (b ^ c) := by
        apply (FiniteMultiplicity.multiplicity_le_multiplicity_iff h_v_ab h_v_bc).mpr
        intro n h_dvd
        exact Nat.dvd_trans h_dvd h₂
      rw [FiniteMultiplicity.multiplicity_pow hp h_v_a, FiniteMultiplicity.multiplicity_pow hp h_v_b, mul_comm , mul_comm c ] at h_le
      exact h_le
    -- Valuation inequalities $v_a * c ≤ v_c * b$ from divisibility.
    have h_val_2 : v_a * c ≤ v_c * b := by
      unfold v_a v_c
      have h_v_ac : FiniteMultiplicity p (a ^ c) := by
        rw [Nat.finiteMultiplicity_iff]
        split_ands
        · exact Prime.ne_one hp
        · have : 0 < a ^ c := pow_pos (by nlinarith) c
          exact this
      have h_v_cb : FiniteMultiplicity p (c ^ b) := by
        rw [Nat.finiteMultiplicity_iff]
        split_ands
        · exact Prime.ne_one hp
        · have : 0 < c ^ b := pow_pos (by nlinarith) b
          exact this
      have h_le : multiplicity p (a ^ c) ≤ multiplicity p (c ^ b) := by
        apply (FiniteMultiplicity.multiplicity_le_multiplicity_iff h_v_ac h_v_cb).mpr
        intro n h_dvd
        exact Nat.dvd_trans h_dvd h₃
      rw [FiniteMultiplicity.multiplicity_pow hp h_v_a, FiniteMultiplicity.multiplicity_pow hp h_v_c, mul_comm , mul_comm b ] at h_le
      exact h_le
    -- Derive $v_a ^ 2 ≤ v_b * v_c$ by multiplying two inequalities.
    have h_val_prod : v_a ^ 2 ≤ v_b * v_c := by
      have h_b_pos : 0 < (b : ℝ) := by exact_mod_cast h₀
      have h_c_pos : 0 < (c : ℝ) := by exact_mod_cast h₁
      have h_val_1_real : (v_a : ℝ) ≤ v_b * c / b  := by
        apply (le_div_iff₀ h_b_pos).mpr
        exact_mod_cast h_val_1
      have h_val_2_real : (v_a : ℝ) ≤  v_c * b / c  := by
        apply (le_div_iff₀ h_c_pos).mpr
        exact_mod_cast h_val_2
      have h_va_nonneg : 0 ≤ (v_a : ℝ) := Nat.cast_nonneg v_a
      nlinarith
    -- Apply AM-GM inequality.
    have h_am_gm : (v_a : ℝ) ≤ (v_b + v_c) / 2 := by
      have h_v_a_nonneg : 0 ≤ (v_a : ℝ) := Nat.cast_nonneg v_a
      have h_v_b_nonneg : 0 ≤ (v_b : ℝ) := Nat.cast_nonneg v_b
      have h_v_c_nonneg : 0 ≤ (v_c : ℝ) := Nat.cast_nonneg v_c
      have h_sqrt_va : sqrt ((v_a : ℝ) ^ 2) = (v_a : ℝ) := sqrt_sq h_v_a_nonneg
      rw [← h_sqrt_va]
      have : sqrt ((v_b :ℝ ) * (v_c :ℝ )) ≤ (v_b + v_c) / 2 := am_gm_ineq v_b v_c h_v_b_nonneg h_v_c_nonneg
      have : sqrt ((v_a : ℝ) ^ 2) ≤ (v_b + v_c) / 2 := by
        have : (v_a : ℝ) ^ 2 ≤ ((v_b :ℝ) * (v_c :ℝ)) := by exact_mod_cast h_val_prod
        have : sqrt ((v_a : ℝ) ^ 2) ≤ sqrt ((v_b :ℝ ) * (v_c :ℝ)) := by exact Real.sqrt_le_sqrt this
        nlinarith
      exact this
    have h_final : (2 * v_a : ℝ) ≤ v_b + v_c := by nlinarith
    exact_mod_cast h_final
  -- Conclude $a^2 ∣ b * c$.
  have h_div : a ^ 2 ∣ b * c := by
    have h₁: a ^ 2 ≠ 0 := by nlinarith
    have h₂: b * c ≠ 0 := by nlinarith
    have h_val_le : ∀ p, Nat.Prime p → (a ^ 2).factorization p ≤ (b * c).factorization p := by
      intro p hp
      have hp' : Fact (Nat.Prime p) := by
        exact Fact.mk hp
      have hp'' : Prime p := by
        exact Nat.prime_iff.mp hp
      have h_v_a : FiniteMultiplicity p a := by
        rw [Nat.finiteMultiplicity_iff]
        split_ands
        · exact Prime.ne_one hp''
        · nlinarith
      have h_v_bc : FiniteMultiplicity p (b * c) := by
        rw [Nat.finiteMultiplicity_iff]
        split_ands
        · exact Prime.ne_one hp''
        · nlinarith
      rw [Nat.factorization_def (a^2) hp, Nat.factorization_def (b*c) hp, padicValNat_def (by nlinarith) ,
        padicValNat_def (by nlinarith), FiniteMultiplicity.multiplicity_pow hp'' h_v_a, multiplicity_mul hp'' h_v_bc]
      exact h_val p hp''
    exact (Nat.factorization_prime_le_iff_dvd h₁ h₂).mp h_val_le
  exact h_div