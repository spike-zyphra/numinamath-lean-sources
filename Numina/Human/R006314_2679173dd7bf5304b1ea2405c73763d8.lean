import Mathlib

/-
Let b be a natural number such that b > 4. Let d_0 and e_0 be natural numbers such that d_0 < b and e_0 < b.
Let N_1 be the number 4 × b^2 + 1 × b + d_0 and N_2 be the number 2 × b^2 + 1 × b + e_0.
Assume $N₁ ≥ N₂. Determine the units digit of N₁ - N₂ in base b is equal to (b + d_0 - e_0) mod b.
-/

theorem base_b (b : ℕ) (hb : 4 < b) (d₀ e₀ N₁ N₂ : ℕ) (he₀ : e₀ < b)
    (hN₁ : N₁ = 4 * b ^ 2 + b + d₀) (hN₂ : N₂ = 2 * b ^ 2 + b + e₀)
    (hN₁₂ : N₁ ≥ N₂) :
    (N₁ - N₂) % b = (b + d₀ - e₀) % b := by
  -- [Step 1] Expand N₁ and N₂ definitions
  rw [hN₁, hN₂]

  -- [Step 2] Case analysis based on digit comparison
  by_cases hpos : d₀ ≥ e₀
  · -- [Case 1] When d₀ ≥ e₀ (no borrow needed)
    -- [Step 2.1] Compute exact difference
    have hdiff : ((4 * b ^ 2 + b + d₀) - (2 * b ^ 2 + b + e₀)) = 2 * b ^ 2 + (d₀ - e₀) := by omega
    rw [hdiff]

    -- [Step 2.2] Prove 2*b² ≡ 0 mod b
    have h0 : (2 * b ^ 2) % b = 0 := by
      have t : 2 * b ^ 2 = b * (2 * b) := by ring
      rw [t]
      simp  -- Any multiple of b mod b is 0

    -- [Step 2.3] Modular arithmetic simplification
    calc
      (2 * b ^ 2 + (d₀ - e₀)) % b
          = ((2 * b ^ 2) % b + (d₀ - e₀) % b) % b := by simp [Nat.add_mod]
      _ = (0 + (d₀ - e₀) % b) % b := by rw [h0]
      _ = (d₀ - e₀) % b := by simp

    -- [Step 2.4] Show equivalence to target form
    have h1 : b + d₀ - e₀ = b + (d₀ - e₀) := by omega
    have h2 : (b + (d₀ - e₀)) % b = (d₀ - e₀) % b := by
      simp  -- Adding b doesn't change modulo when d₀ ≥ e₀
    rw [h1, h2]

  · -- [Case 2] When d₀ < e₀ (borrow needed)
    -- [Step 3.1] Define helper terms
    let bd : ℕ := b + d₀  -- Combined term representing borrowed base
    let powb : ℕ := 2 * b ^ 2 - b  -- Adjusted power term

    -- [Step 3.2] Prove helper term properties
    have bdpos : bd - e₀ > 0 := by omega  -- Positive after borrow
    have bdmod : (bd - e₀) % b = (b + d₀ - e₀) % b := by
      unfold bd  -- Just definitional equality
      rfl

    have powbpos : powb > 0 := by
      unfold powb
      have t1 : powb - b > 0 := by
        unfold powb
        simp only [Nat.sub_sub]
        rw [← Nat.two_mul]
        simp [Nat.mul_sub_left_distrib]
        rw [pow_two]
        simp [Nat.mul_sub_left_distrib]
        omega
      unfold powb at t1
      omega

    -- [Step 3.3] Prove powb ≡ 0 mod b
    have powbmod : powb % b = 0 := by
      unfold powb
      have t2 : (2 * b ^ 2 - b) % b = (2 * b ^ 2) % b := by
        refine Eq.symm (Nat.mod_eq_sub_mod ?_)
        unfold powb at powbpos
        omega
      have t3 : 2 * b ^ 2 % b = 0 := by
        have t: 2 * b ^ 2 = b * (2 * b) := by ring
        rw [t]
        rw [← mul_assoc]
        simp
      rw [t2]
      exact t3

    -- [Step 3.4] Rewrite difference using borrowed form
    have heq : ((4 * b ^ 2 + b + d₀) - (2 * b ^ 2 + b + e₀))
              = (2 * b ^ 2 - b) + (b + d₀ - e₀) := by
      repeat rw [tsub_add_eq_tsub_tsub]
      calc
        _ = 2 * b ^ 2 + b - b + d₀ - e₀ := by omega
        _ = 2 * b ^ 2 - b + b + d₀ - e₀ := by omega
        _ = (2 * b ^ 2 - b) + (b + d₀ - e₀) := by omega

    -- [Step 3.5] Apply modular arithmetic
    rw [heq]
    have heq' : ((2 * b ^ 2 - b) + (b + d₀ - e₀)) % b
               = ((2 * b ^ 2 - b) % b + (b + d₀ - e₀) % b) % b := by
      simp [Nat.add_mod]
    rw [heq']
    rw [powbmod]
    rw [zero_add]
    simp  -- Final simplification
