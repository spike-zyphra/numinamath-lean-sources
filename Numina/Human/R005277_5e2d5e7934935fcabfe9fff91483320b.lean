import Mathlib

/- Déterminer tous les triplets $(x, y, z)$ d'entiers naturels satisfaisant l'équation:

$$
2^{x}+3^{y}=z^{2}
$$-/
theorem number_theory_607325 :
    {(x, y, z) : ℕ × ℕ × ℕ | 2 ^ x + 3 ^ y = z ^ 2} = {(0, 1, 2), (3, 0, 3), (4, 2, 5)} := by
  -- Simplify the goal into two parts.
  ext ⟨x, y, z⟩
  apply Iff.intro
  . -- First show that 2 ^ x + 3 ^ y = z ^ 2 implies that (x, y, z) = (0, 1, 2), (3, 0, 3) or (4, 2, 5).
    intro h
    simp at h
    by_cases h₀ : x < 2
    . -- Suppose that x < 2.
      interval_cases x
      . -- Suppose that x = 0.
        by_cases h₁ : y < 2
        . interval_cases y
          . -- Suppose x = 0 and y = 0. Contradiction.
            simp [h₁] at h
            -- Contradiction is derived from 2 = z².
            linarith only [show 1 < z by nlinarith, show z < 2 by nlinarith]
          . -- Suppose x = 0 and y = 1. We get one of the solutions.
            replace h : z ^ 2 = 2 ^ 2 := by
              linarith only [h]
            rw [sq_eq_sq₀ (by simp) (by norm_num)] at h
            -- The solution is (0, 1, 2).
            tauto
        . -- Suppose x = 0 and y ≥ 2. Contradiction.
          -- We have 3 ^ y = (z - 1)(z + 1).
          replace h : 3 ^ y = (z + 1) * (z - 1) := by
            rw [<-Nat.sq_sub_sq, <-h, add_comm]
            simp
          replace h₀ : y ≥ 2 := by
            simp_all
          -- Write z - 1 = 3 ^ a and z + 1 = 3 ^ b.
          replace h₁ : z - 1 ∣ 3 ^ y := by
            rw [h]
            apply Nat.dvd_mul_left
          have h₂ : z + 1 ∣ 3 ^ y := by
            rw [h]
            apply Nat.dvd_mul_right
          rw [Nat.dvd_prime_pow (Nat.prime_three)] at h₁ h₂
          -- Write z - 1 = 3 ^ a and z + 1 = 3 ^ b.
          obtain ⟨a, h₁, h₃⟩ := h₁
          obtain ⟨b, h₂, h₄⟩ := h₂
          -- Show that a < b.
          have h₅ : 3 ^ a < 3 ^ b := by
            omega
          rw [Nat.pow_lt_pow_iff_right (by norm_num)] at h₅
          -- Verify that z > 1.
          have h₆ : z > 0 := by
            by_contra!
            simp at this
            rw [show z + 1 = 3 ^ 0 by norm_num [this]] at h₄
            apply Nat.pow_right_injective (by norm_num) at h₄
            omega
          -- We have 2 = 3 ^ a ⬝ (3 ^ (b - a) - 1).
          have h₇ : 2 = 3 ^ a * (3 ^ (b - a) - 1) := by
            rw [Nat.mul_sub, <-Nat.pow_add, add_comm, Nat.sub_add_cancel (le_of_lt h₅), <-h₄, <-h₃]
            omega
          -- Evaluate the equation in padic 3 to show that a = 0.
          have h₈ : a = 0 := by
            replace h₇ := congr_arg (padicValNat 3 ·) h₇
            simp at h₇
            -- Verify that 3 ^ (b - a) - 1 > 0.
            have h₉ : 3 ^ (b - a) - 1 > 0 := by
              calc
                _ ≥ 3 ^ 1 - 1 := by
                  rw [ge_iff_le, Nat.sub_le_sub_iff_right, Nat.pow_le_pow_iff_right (by norm_num)]
                  omega
                  apply Nat.one_le_pow _ _ (by norm_num)
                _ > 0 := by
                  norm_num
            -- Verify that 3 ∤ 3 ^ (b - a) - 1.
            have h₁₀ : ¬3 ∣ 3 ^ (b - a) - 1 := by
              -- Assume on the contrary that 3 ∣ 3 ^ (b - a) - 1, then 3 ∣ 1.
              by_contra! h₁₀
              zify at h₁₀
              rw [Int.ofNat_sub (by omega)] at h₁₀
              zify at h₁₀
              apply Int.dvd_iff_dvd_of_dvd_sub at h₁₀
              norm_cast at h₁₀
              norm_num at h₁₀
              -- We shall show that 3 ∣ 3 ^ (b - a), so the hypothesis h₁₀ is absurd.
              absurd h₁₀
              apply dvd_pow_self
              omega
            rw [padicValNat_primes (by norm_num), padicValNat.mul (by positivity) h₉.ne', show padicValNat 3 (3 ^ (b - a) - 1) = 0 by apply padicValNat.eq_zero_of_not_dvd h₁₀] at h₇
            simp at h₇
            tauto
          -- We have b = 1.
          norm_num [h₈] at h₇
          replace h₇ : 3 ^ b = 3 ^ 1 := by
            omega
          apply Nat.pow_right_injective (by norm_num) at h₇
          rw [h₃, h₄, h₈, h₇, <-Nat.pow_add] at h
          -- We have y = 1, which is a contradiction.
          apply Nat.pow_right_injective (by norm_num) at h
          omega
      . -- Suppose that x = 1.
        by_cases h₁ : y < 2
        . interval_cases y
          . -- Suppose x = 1 and y = 0. Contradiction.
            simp [h₁] at h
            -- Contradiction is derived from 3 = z².
            linarith only [show 1 < z by nlinarith, show z < 2 by nlinarith]
          . -- Suppose x = 1 and y = 1. Contradiction.
            simp [h₁] at h
            -- Contradiction is derived from 5 = z².
            linarith only [show 2 < z by nlinarith, show z < 3 by nlinarith]
        . -- Suppose that x = 1 and y ≥ 2. Contradiction.
          simp at h₁
          -- Consider modulo 9.
          replace h := congr_arg (· % 9) h
          apply Nat.exists_eq_add_of_le at h₁
          obtain ⟨y', h₁⟩ := h₁
          simp [h₁, Nat.pow_add] at h
          -- However, it is impossible that z ^ 2 % 9 = 2.
          have h₂ : z ^ 2 % 9 ≠ 2 := by
            -- Show that any square modulo 9 is either 0, 1, 4 or 7.
            have h9residue : ∀ a : ℕ, a ^ 2 % 9 = 0 ∨ a ^ 2 % 9 = 1 ∨ a ^ 2 % 9 = 4 ∨ a ^ 2 % 9 = 7 := by
              intro a
              have : a % 9 = 0 ∨ a % 9 = 1 ∨ a % 9 = 2 ∨ a % 9 = 3 ∨ a % 9 = 4 ∨ a % 9 = 5 ∨ a % 9 = 6 ∨ a % 9 = 7 ∨ a % 9 = 8 := by
                omega
              rcases this with (h | h | h | h | h | h | h | h | h)
              <;> simp [h, pow_two, Nat.mul_mod, Nat.add_mod]
            specialize h9residue z
            omega
          tauto
    . -- Suppose that x ≥ 2.
      simp at h₀
      -- We have y even.
      have h₁ : Even y := by
        -- Assume on the contrary that y is odd, then the equation would be absurd modulo 4.
        by_contra! h₁
        simp [Odd] at h₁
        obtain ⟨y', h₁⟩ := h₁
        replace h := congr_arg (· % 4) h
        apply Nat.exists_eq_add_of_le at h₀
        obtain ⟨x', h₀⟩ := h₀
        simp [h₁, h₀, Nat.pow_add, Nat.pow_mul, Nat.pow_mod, Nat.mul_mod, Nat.add_mod] at h
        norm_num at h
        rw [<-Nat.pow_mod] at h
        -- Show that any square modulo 4 is either 0 or 1.
        have h4residue : ∀ a : ℕ, a ^ 2 % 4 = 0 ∨ a ^ 2 % 4 = 1 := by
          intro a
          have : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by
            omega
          rcases this with (h | h | h | h)
          <;> simp [h, pow_two, Nat.mul_mod, Nat.add_mod]
        specialize h4residue z
        omega
      -- Write y = 2w.
      obtain ⟨w, h₁⟩ := h₁
      rw [<-mul_two] at h₁
      rw [h₁, pow_mul] at h
      -- We have 2 ^ x = (z + 3 ^ w) (z - 3 ^ w), and z > 3 ^ w.
      have h₂ : (3 ^ w) ^ 2 < z ^ 2 := by
        linarith only [show 2 ^ x > 0 by positivity, h]
      rw [Nat.pow_lt_pow_iff_left (by norm_num)] at h₂
      replace h₀ : 2 ^ x = (z + 3 ^ w) * (z - 3 ^ w) := by
        rw [<-Nat.sq_sub_sq, <-Nat.pow_mul, <-h, Nat.pow_mul, Nat.add_sub_cancel]
      -- Write z - 3 ^ w and z + 3 ^ w as powers of two.
      have h₃ : z - 3 ^ w ∣ 2 ^ x := by
        rw [h₀]
        apply Nat.dvd_mul_left
      have h₄ : z + 3 ^ w ∣ 2 ^ x := by
        rw [h₀]
        apply Nat.dvd_mul_right
      rw [Nat.dvd_prime_pow (Nat.prime_two)] at h₃ h₄
      -- Write z - 3 ^ w = 2 ^ a and z + 3 ^ w = 2 ^ b.
      obtain ⟨a, h₃, h₅⟩ := h₃
      obtain ⟨b, h₄, h₆⟩ := h₄
      -- Verify that z - 3 ^ w < z + 3 ^ w.
      have h₇ : z - 3 ^ w < z + 3 ^ w := by
        calc
          z - 3 ^ w ≤ z := by apply Nat.sub_le
          _ < z + 3 ^ w := by linarith only [show 0 < 3 ^ w by positivity]
      -- We have a < b.
      have h₈ : 2 ^ a < 2 ^ b := by
        omega
      rw [Nat.pow_lt_pow_iff_right (by norm_num)] at h₈
      -- We have 2 ⬝ 3 ^ w = 2 ^ a ⬝ (2 ^ (b - a) - 1)
      have h₉ : 2 * 3 ^ w = 2 ^ a * (2 ^ (b - a) - 1) := by
        rw [Nat.mul_sub, <-Nat.pow_add, add_comm, Nat.sub_add_cancel (le_of_lt h₈)]
        omega
      -- Evalutate the equation in padic 2 to show that a = 1.
      have h₁₀ : a = 1 := by
        replace h₉ := congr_arg (padicValNat 2 ·) h₉
        simp at h₉
        nth_rw 2 [show 2 = 2 ^ 1 by norm_num] at h₉
        -- Verify that 2 ^ (b - a) - 1 > 0.
        have h₁₀ : 2 ^ (b - a) - 1 > 0 := by
          calc
            _ ≥ 2 ^ 1 - 1 := by
              apply Nat.sub_pos_of_lt
              apply Nat.one_lt_pow (by omega)
              norm_num
            _ > 0 := by
              norm_num
        -- Verify that 2 ∤ 2 ^ (b - a) - 1.
        have h₁₁ : ¬2 ∣ 2 ^ (b - a) - 1 := by
          -- Assume on the contrary that 2 ∣ 2 ^ (b - a) - 1, then 2 ∣ 1.
          by_contra! h₁₁
          zify at h₁₁
          rw [Int.ofNat_sub (by omega)] at h₁₁
          zify at h₁₁
          apply Int.dvd_iff_dvd_of_dvd_sub at h₁₁
          norm_cast at h₁₁
          norm_num at h₁₁
          omega
        rw [padicValNat_mul_pow_left _ _ (by norm_num), padicValNat.mul (by positivity) h₁₀.ne', show padicValNat 2 (2 ^ (b - a) - 1) = 0 by apply padicValNat.eq_zero_of_not_dvd h₁₁] at h₉
        simp_all
      -- Now we have 2 ^ (b - 1) = 3 ^ w + 1.
      simp [h₁₀] at h₉
      replace h₉ : 2 ^ (b - 1) = 3 ^ w + 1 := by
        omega
      clear h₈
      by_cases h₈ : w = 0
      . -- Suppose w = 0.
        rw [show 3 ^ w + 1 = 2 ^ 1 by norm_num [h₈]] at h₉
        apply Nat.pow_right_injective (by rfl) at h₉
        -- We have b - 1 = 1, a = 1, x = 3.
        rw [h₅, h₆, show b = 2 by omega, h₁₀, <-Nat.pow_add] at h₀
        apply Nat.pow_right_injective (by rfl) at h₀
        -- We have x = 3, y = 0, z = 3. We get one of the solutions.
        simp [h₀, h₈] at h
        rw [show 9 = 3 ^ 2 by norm_num, sq_eq_sq₀ (by simp) (by norm_num)] at h
        simp [h₈] at h₁
        simp_all
      . -- Suppose w > 0.
        -- We have b - 1 even.
        have h₁₁ : Even (b - 1) := by
          by_contra! h₁₁
          -- If not, we derive a contradiction by considering modulo 3.
          simp [Odd] at h₁₁
          obtain ⟨x', h₁₁⟩ := h₁₁
          replace h₉ := congr_arg (· % 3) h₉
          simp [h₁₁, Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.add_mod, Nat.pow_mod] at h₉
          norm_num [Nat.zero_pow (show 0 < w by omega)] at h₉
        -- Let b - 1 = 2k.
        obtain ⟨k, h₁₁⟩ := h₁₁
        rw [h₁₁] at h₉
        -- We have 3 ^ w = (2 ^ k - 1) (2 ^ k + 1).
        replace h₉ : 3 ^ w = (2 ^ k + 1) * (2 ^ k - 1) := by
          rw [<-Nat.sq_sub_sq, Nat.pow_two, <-Nat.pow_add]
          omega
        -- Write 2 ^ k - 1 = 3 ^ m and 2 ^ k + 1 = 3 ^ n.
        have h₁₂ : 2 ^ k - 1 ∣ 3 ^ w := by
          rw [h₉]
          apply Nat.dvd_mul_left
        have h₁₃ : 2 ^ k + 1 ∣ 3 ^ w := by
          rw [h₉]
          apply Nat.dvd_mul_right
        rw [Nat.dvd_prime_pow (Nat.prime_three)] at h₁₂ h₁₃
        obtain ⟨m, h₁₂, h₁₄⟩ := h₁₂
        obtain ⟨n, h₁₃, h₁₅⟩ := h₁₃
        -- Show that m ≤ n.
        have h₁₆ : 3 ^ m ≤ 3 ^ n := by
          rw [<-h₁₄, <-h₁₅]
          calc
            2 ^ k - 1 ≤ 2 ^ k := by apply Nat.sub_le
            _ ≤ 2 ^ k + 1 := by omega
        rw [Nat.pow_le_pow_iff_right (by norm_num)] at h₁₆
        -- We have 2 ^ k - 1 ∣ 2 ^ k + 1.
        have h₁₇ : 2 ^ k - 1 ∣ 2 ^ k + 1 := by
          rw [h₁₄, h₁₅]
          apply Nat.pow_dvd_pow _ h₁₆
        -- We have 2 ^ k - 1, 2 ^ k + 1 coprime.
        have h₁₈ : Nat.Coprime (2 ^ k - 1) (2 ^ k + 1) := by
          have : 1 ≤ 2 ^ k := by
            apply Nat.one_le_pow _ _ (by norm_num)
          rw [show 2 ^ k + 1 = 2 ^ k - 1 + 2 by omega, Nat.coprime_add_iff_right (by rfl), Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (Nat.prime_two)]
          -- Show that 0 < k.
          have h₁₈ : 0 < k := by
            by_contra!
            simp at this
            norm_num [this] at h₁₄
            linarith only [h₁₄, show 0 < 3 ^ m by positivity]
          -- We prove 2 ∤ 2 ^ k - 1 by contradiction.
          by_contra!
          rw [<-Nat.modEq_iff_dvd'] at this
          symm at this
          apply Nat.mod_eq_of_modEq at this
          norm_num [Nat.pow_mod, Nat.zero_pow h₁₈] at this
          omega
        -- We have 2 ^ k - 1 = 1, and hence 2 ^ k + 1 = 3 ^ w.
        apply Nat.Coprime.eq_one_of_dvd h₁₈ at h₁₇
        simp [h₁₇] at h₉
        -- We have w = 1 by comparing the two equations.
        replace h₉ : 3 ^ w = 3 ^ 1 := by
          omega
        apply Nat.pow_right_injective (by norm_num) at h₉
        -- We have y = 2 and x = 4.
        simp [h₉] at h₁
        replace h₁₇ : 2 ^ k = 2 ^ 1 := by
          omega
        apply Nat.pow_right_injective (by norm_num) at h₁₇
        rw [h₅, h₆, h₁₀, show b = 3 by omega, <-Nat.pow_add] at h₀
        apply Nat.pow_right_injective (by rfl) at h₀
        -- We have z = 5. We get one of the solutions.
        replace h : z ^ 2 = 5 ^ 2 := by
          simp_all
        apply Nat.pow_left_injective (by norm_num) at h
        simp
        tauto
  . -- Now show that (x, y, z) = (0, 1, 2), (3, 0, 3) or (4, 2, 5) implies that 2 ^ x + 3 ^ y = z ^ 2.
    simp
    rintro (⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩)
    <;> simp_all
