import Mathlib

open Real Complex Polynomial

/- Let $\omega = \cos\frac{2\pi}{7} + i \cdot \sin\frac{2\pi}{7},$ where $i = \sqrt{-1}.$ Find the value of the product
$$
\prod_{k=0}^6 \left(\omega^{3k} + \omega^k + 1\right).
$$
 -/
theorem algebra_92963 (ω : ℂ) (hω : ω = exp (I * 2 * π / 7)) : ∏ k ∈ Finset.range 7, (ω^(3 * k) + ω^k + 1) = 24 := by
    -- first convert powers to int for ease of using subtraction
    suffices ∏ k ∈ Finset.range 7, (ω^(3 * (k:ℤ)) + ω^(k:ℤ) + 1) = 24 by
      norm_cast at this
    -- prove ω ≠ 0, ω^7 = 1, ω^21 = 1
    have h_om_nz : ω ≠ 0 := by rw [hω]; simp
    have h_om_7 : ω^(7:ℤ) = 1 := by
      norm_cast; rw [hω, ← Complex.exp_nat_mul]
      calc
        cexp (7 * (I * 2 * π / 7)) = cexp (1 * (2 * π * I)) := by ring_nf
        _ = 1 := by simp
    have h_om_21 : ω^(21:ℤ) = 1 := by
      norm_cast; rw [hω, ← Complex.exp_nat_mul]
      calc
        cexp (21 * (I * 2 * π / 7)) = cexp (3 * (2 * π * I)) := by ring_nf
        _ = 1 := by exact Complex.exp_nat_mul_two_pi_mul_I 3
    -- prove for 0 < n < 7, ω^n ≠ 1, so that division by ω^n - 1 can be done
    have h_om_not_1 (n:ℕ) (h₁ : 0 < n) (h₂ : n < 7) : ω^n ≠ 1 := by
      rw [hω, ← Complex.exp_nat_mul]
      simp
      by_contra heq_one
      norm_cast at heq_one
      have := Complex.exp_eq_one_iff.mp heq_one
      obtain ⟨m, hm⟩ := this
      have : (n:ℂ) = m * 7 := by
        have : 2 * π * I ≠ 0 := by
          by_contra h
          simp at h
          exact absurd h (pi_ne_zero)
        calc
          (n:ℂ) = n * (2 * π * I) / (2 * π * I) := by
            field_simp
          _ = n * (I * 2 * π / 7) * 7 / (2 * π * I) := by ring
          _ = m * 7 * (2 * π * I)  / (2 * π * I) := by rw [hm]; ring
          _ = m * 7 := by field_simp
      norm_cast at this
      interval_cases n
      all_goals omega
    -- define f(n) = ω^(3n) + ω^n + 1 to make target easier to work with
    set f : ℤ → ℂ := fun n ↦ ω^(3*n) + ω^n + 1 with hf
    -- prove f(0) = 1, other 6 terms will be handled separately
    have hf0 : f 0 = 3 := by
      dsimp [f]
      simp
      norm_num
    -- prove that for 0 < n < 7, ω^0 + ... + ω^6 = 0, will be used later
    have hω_sum (n: ℤ) (h₁ : 0 < n) (h₂ : n < 7) : ω^0 + ω^n + ω^(n*2) + ω^(n*3) + ω^(n*4) + ω^(n*5) + ω^(n*6) = 0 := by
      have : ω^n ≠ 1 := by
        have : n = n.toNat := by rw [Int.toNat_of_nonneg]; linarith
        rw [this]; rw [this] at h₁; rw [this] at h₂
        norm_cast; norm_cast at h₁; norm_cast at h₂
        apply h_om_not_1 <;> assumption
      have : ω^n - 1 ≠ 0 := by
        by_contra h'
        have : ω^n = 0 + 1 := by exact sub_eq_iff_eq_add.mp h'
        norm_num at this
        contradiction
      have aux₁ : (ω ^ n) ^ (2:ℤ) = ω ^ (n * 2) := by exact Eq.symm (zpow_mul ω n 2)
      norm_cast at aux₁
      have aux₂ : ω ^ (n * 7) = (ω^(7:ℤ))^n := by
        rw [← zpow_mul]
        ring_nf
      calc
        ω^0 + ω^n + ω^(n*2) + ω^(n*3) + ω^(n*4) + ω^(n*5) + ω^(n*6) = (ω^0 + ω^n + ω^(n*2) + ω^(n*3) + ω^(n*4) + ω^(n*5) + ω^(n*6)) * (ω^n - 1) / (ω^n - 1) := by field_simp
        _ = 0 / (ω^n-1) := by
          congr
          ring_nf
          repeat rw [← zpow_add₀ h_om_nz]
          ring_nf
          rw [aux₁, aux₂, h_om_7]
          simp
        _ = 0 := by simp
    -- by algebraic manipulations and previous facts, prove f(n) * f(7-n) = 2, this will allow handling f(1), ..., f(6)
    have hf_symm (n: ℤ) (h₁ : 0 < n) (h₂ : n < 7) : f n * f (7-n) = 2 := by
      dsimp [f]
      calc
        (ω ^ (3*n) + ω ^ n + 1) * (ω ^ (3*(7 - n)) + ω ^ (7 - n) + 1) = (ω ^ (3*n) + ω ^ n + 1) * (ω^(21:ℤ)*ω^(-3*n) + ω^(7:ℤ)*ω^(-n) + 1) := by
          congr
          repeat (ring_nf; rw [← zpow_add₀ h_om_nz]; ring_nf)
        _ = (ω ^ (3*n) + ω ^ n + 1) * (ω^(-3*n) + ω^(-n) + 1) := by rw [h_om_7, h_om_21]; simp
        _ = 1 + ω ^ (n * 3) + 2 + ω ^ (n * 2) + ω ^ n + ω ^ (-n * 2) + ω ^ (-n * 3) + ω ^ (-n) := by
          ring_nf
          repeat rw [← zpow_add₀ h_om_nz]
          ring_nf; norm_num; ring
        _ = 2 + (ω^(-n*3) + ω^(-n*2) + ω^(-n) + 1 + ω^n + ω^(n*2) + ω^(n*3)) := by ring
        _ = 2 + ω^(-n*3)*(ω^0 + ω^n + ω^(n*2) + ω^(n*3) + ω^(n*4) + ω^(n*5) + ω^(n*6)) := by
          ring_nf
          repeat rw [← zpow_add₀ h_om_nz]
          simp only [neg_add_cancel, zpow_zero]
          ring_nf
        _ = 2 := by
          rw [hω_sum n h₁ h₂]
          simp
    -- auxilary theorem for casting between Nat and Int
    have aux (n: ℕ) : (ω^(3 * n) + ω^n + 1) = f n := by
      dsimp [f]
      norm_cast
    -- express the product as 7 terms
    simp only [ Finset.prod_range, Fin.prod_univ_seven, Fin.isValue, Fin.val_zero,
      Fin.val_one, Fin.val_two, Nat.cast_ofNat, Int.reduceMul]
    norm_cast
    rw [aux 0, aux 1, aux 2]
    have : (↑(@Fin.val 7 3):ℕ) = 3 := by norm_cast
    rw [this, aux 3]
    have : (↑(@Fin.val 7 4):ℕ) = 4 := by norm_cast
    rw [this, aux 4]
    have : (↑(@Fin.val 7 5):ℕ) = 5 := by norm_cast
    rw [this, aux 5]
    have : (↑(@Fin.val 7 6):ℕ) = 6 := by norm_cast
    rw [this, aux 6]
    norm_cast
    -- finally write f(0) as 3 and grouping rest 6 terms by symmetry get 2 * 2 * 2
    calc
      f 0 * f 1 * f 2 * f 3 * f 4 * f 5 * f 6 = 3 * (f 1 * f (7-1)) * (f 2 * f (7-2)) * (f 3 * f (7-3)) := by rw [hf0]; simp; ring
      _ = 3 * 2 * 2 * 2 := by
        rw [hf_symm, hf_symm, hf_symm]
        all_goals norm_num
      _ = 24 := by norm_num