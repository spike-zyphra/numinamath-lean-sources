import Mathlib

/- 17. (HKG 4) Find all positive integer solutions $x, y, z$ of the equation $3^{x}+$ $4^{y}=5^{z}$.-/
theorem number_theory_24352 :
    {(x, y, z) : ℕ × ℕ × ℕ | 0 < x ∧ 0 < y ∧ 0 < z ∧ 3 ^ x + 4 ^ y = 5 ^ z} = {(2, 2, 2)} := by
  ext ⟨x, y, z⟩
  -- Break the goal into two parts.
  simp
  apply Iff.intro
  . -- First assume that x, y, z > 0 and 3^x + 4^y = 5^z.
    rintro ⟨hx, hy, hz, h⟩
    -- Examine the equation modulo 4.
    have h₀ := congr_arg (· % 4) h
    simp [Nat.pow_mod, Nat.add_mod, zero_pow hy.ne'] at h₀
    norm_num at h₀
    -- Show that x is even.
    replace h₀ : Even x := by
      -- Assume on the contrary that x is odd.
      by_contra!
      simp [Odd] at this
      obtain ⟨x, rfl⟩ := this
      simp [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod] at h₀
    -- Substitute x = 2x₀ into the equation.
    rw [even_iff_two_dvd, dvd_iff_exists_eq_mul_right] at h₀
    obtain ⟨x₀, rfl⟩ := h₀
    -- Examine the equation modulo 3.
    have h₀ := congr_arg (· % 3) h
    simp [Nat.pow_mod, Nat.add_mod, zero_pow hx.ne'] at h₀
    norm_num at h₀
    -- Show that z is even.
    replace h₀ : Even z := by
      -- Assume on the contrary that z is odd.
      by_contra!
      simp [Odd] at this
      obtain ⟨z, rfl⟩ := this
      simp [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod] at h₀
    -- Substitute z = 2z₀ into the equation.
    rw [even_iff_two_dvd, dvd_iff_exists_eq_mul_right] at h₀
    obtain ⟨z₀, rfl⟩ := h₀
    -- Show that 3 ^ (2x₀) ≤ 5 ^ (2z₀) from the equation.
    have h₀ : 3 ^ (2 * x₀) ≤ 5 ^ (2 * z₀) := by
      linarith [show 0 < 4 ^ y by positivity]
    -- We have 2 ^ (2y) = (5 ^ z₀ + 3 ^ x₀)(5 ^ z₀ - 3 ^ x₀).
    have h₁ : 2 ^ (2 * y) = (5 ^ z₀ + 3 ^ x₀) * (5 ^ z₀ - 3 ^ x₀) := by
      rw [<-Nat.sq_sub_sq, <-Nat.pow_mul, <-Nat.pow_mul, Nat.pow_mul, mul_comm _ 2, mul_comm _ 2]
      simp
      omega
    replace h₀ : 3 ^ x₀ ≤ 5 ^ z₀ := by
      rw [<-sq_le_sq₀ (by positivity) (by positivity), <-Nat.pow_mul, <-Nat.pow_mul]
      ring_nf at h₀
      exact h₀
    -- Write 5 ^ z₀ - 3 ^ x₀ = 2 ^ a and 5 ^ z₀ + 3 ^ x₀ = 3 ^ b.
    have h₂ : 5 ^ z₀ - 3 ^ x₀ ∣ 2 ^ (2 * y) := by
      rw [h₁]
      apply Nat.dvd_mul_left
    have h₃ : 5 ^ z₀ + 3 ^ x₀ ∣ 2 ^ (2 * y) := by
      rw [h₁]
      apply Nat.dvd_mul_right
    rw [Nat.dvd_prime_pow (Nat.prime_two)] at h₂ h₃
    obtain ⟨a, h₂, h₄⟩ := h₂
    obtain ⟨b, h₃, h₅⟩ := h₃
    -- Show that a < b.
    have h₆ : 2 ^ a < 2 ^ b := by
      have : 0 < 3 ^ x₀ := by
        positivity
      omega
    rw [Nat.pow_lt_pow_iff_right (by norm_num)] at h₆
    -- Solve to get 2(5 ^ z₀) = 2 ^ a * (2 ^ (b - a) + 1).
    have h₇ : 2 * 5 ^ z₀ = 2 ^ a * (2 ^ (b - a) + 1) := by
      rw [mul_add, <-Nat.pow_add, Nat.add_sub_cancel' (le_of_lt h₆), <-h₄, <-h₅]
      omega
    -- Show that a = 1 by comparing p-adic valuations of both sides.
    replace h₂ : a = 1 := by
      replace h₇ := congr_arg (padicValNat 2 ·) h₇
      simp at h₇
      -- Verify that 2 ∤ 2 ^ (b - a) + 1.
      have h₈ : ¬2 ∣ 2 ^ (b - a) + 1 := by
        -- Assume on the contrary that 2 ∣ 2 ^ (b - a) + 1, then 2 ∣ 1.
        by_contra! h₈
        rw [<-Nat.dvd_add_iff_right] at h₈
        norm_num at h₈
        apply dvd_pow_self _ (by omega)
      iterate 2 rw [padicValNat.mul (by positivity) (by positivity)] at h₇
      rw [@padicValNat_prime_prime_pow _ _ _ (fact_iff.mpr Nat.prime_five) _ (by norm_num), show padicValNat 2 (2 ^ (b - a) + 1) = 0 by apply padicValNat.eq_zero_of_not_dvd h₈] at h₇
      simp at h₇
      exact h₇.symm
    -- Solve to get 3 ^ z₀ = 2 ^ (b - a) - 1.
    have h₈ : 2 * 3 ^ x₀ = 2 ^ a * (2 ^ (b - a) - 1) := by
      rw [Nat.mul_sub, <-Nat.pow_add, Nat.add_sub_cancel' (le_of_lt h₆), <-h₄, <-h₅]
      omega
    simp [h₂] at h₈
    have h₉ := h₈
    -- Get 3 ^ z₀ + 1 = 2 ^ (b - 1) and examine the equation modulo 3.
    rw [<-Nat.Simproc.add_eq_le _ (Nat.one_le_pow _ _ (by norm_num))] at h₈
    replace h₈ := congr_arg (· % 3) h₈
    simp at hx
    simp [Nat.pow_mod, Nat.add_mod, zero_pow hx.ne'] at h₈
    norm_num at h₈
    -- Show that b - 1 is even.
    replace h₈ : Even (b - 1) := by
      -- Assume on the contrary that b - 1 is odd.
      by_contra!
      simp [Odd] at this
      obtain ⟨b, rfl⟩ := this
      simp [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod] at h₈
    -- Now substitute b - 1 = 2b₀ into 3 ^ x₀ = 2 ^ (b - 1) - 1.
    rw [even_iff_two_dvd, dvd_iff_exists_eq_mul_right] at h₈
    obtain ⟨b₀, h₈⟩ := h₈
    -- We get 3 ^ x₀ = (2 ^ b₀ + 1)(2 ^ b₀ - 1).
    rw [h₈, show 1 = 1 ^ 2 by norm_num, Nat.mul_comm, Nat.pow_mul, Nat.sq_sub_sq] at h₉
    -- Write 2 ^ b₀ + 1 = 3 ^ c and 2 ^ b₀ - 1 = 3 ^ d.
    have h₁₀ : 2 ^ b₀ - 1 ∣ 3 ^ x₀ := by
      rw [h₉]
      apply Nat.dvd_mul_left
    have h₁₁ : 2 ^ b₀ + 1 ∣ 3 ^ x₀ := by
      rw [h₉]
      apply Nat.dvd_mul_right
    rw [Nat.dvd_prime_pow (Nat.prime_three)] at h₁₀ h₁₁
    obtain ⟨c, h₁₀, h₁₂⟩ := h₁₀
    obtain ⟨d, h₁₁, h₁₃⟩ := h₁₁
    -- We have c < d.
    have h₁₄ : 3 ^ c < 3 ^ d := by
      have : 0 < 2 ^ b₀ := by
        positivity
      omega
    rw [Nat.pow_lt_pow_iff_right (by norm_num)] at h₁₄
    -- We have 3 ^ c (3 ^ (d - c) - 1) = 2.
    have h₁₅ : 3 ^ c * (3 ^ (d - c) - 1) = 2 := by
      rw [Nat.mul_sub, <-Nat.pow_add, Nat.add_sub_cancel' (le_of_lt h₁₄), <-h₁₃, <-h₁₂]
      have : 0 < 2 ^ b₀ := by
        positivity
      omega
    -- We have c = 0.
    replace h₁₀ : c = 0 := by
      -- Assume on the contrary that c > 0.
      by_contra!
      have : 3 ∣ 2 := by
        calc
          _ ∣ 3 ^ c := dvd_pow_self _ this
          _ ∣ 2 := by
            rw [<-h₁₅]
            apply Nat.dvd_mul_right
      norm_num at this
    -- Show that d = 1.
    simp [h₁₀] at h₁₅
    replace h₁₁ : d = 1 := by
      nth_rw 2 [show 3 = 3 ^ 1 by norm_num] at h₁₅
      apply Nat.pow_right_injective (by norm_num) at h₁₅
      exact h₁₅
    -- Show that b₀ = 1.
    replace h₁₃ : 2 * (2 ^ b₀) = 3 ^ c + 3 ^ d := by
      rw [<-h₁₂, <-h₁₃]
      have : 0 < 2 ^ b₀ := by
        positivity
      omega
    simp [h₁₀, h₁₁] at h₁₃
    replace h₁₃ : 2 ^ b₀ = 2 ^ 1 := by
      linarith
    apply Nat.pow_right_injective (by norm_num) at h₁₃
    -- Show that b = 3.
    replace h₈ : b = 3 := by
      omega
    simp [h₂, h₈] at h₇
    -- Show that z₀ = 1.
    replace h₇ : 5 ^ z₀ = 5 ^ 1 := by
      linarith
    apply Nat.pow_right_injective (by norm_num) at h₇
    -- Show that x₀ = 1.
    simp [h₁₃] at h₉
    nth_rw 2 [show 3 = 3 ^ 1 by norm_num] at h₉
    apply Nat.pow_right_injective (by norm_num) at h₉
    -- Substitute x₀ and z₀ into the original equation to get y = 2.
    simp [h₇, h₉] at h
    replace h : 4 ^ y = 4 ^ 2 := by
      linarith
    apply Nat.pow_right_injective (by norm_num) at h
    -- We have x = y = z = 2 as desired.
    simp [h₇, h, h₉]
  . -- Verify that (2, 2, 2) is a solution.
    rintro ⟨rfl, rfl, rfl⟩
    norm_num
