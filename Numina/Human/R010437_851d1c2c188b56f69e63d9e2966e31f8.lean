import Mathlib
open Nat

/- Soient $a, b$ deux entiers relatifs. Montrer que, si ni $a$, ni $b$ n'est multiple de 3 , alors $a^{4}-b^{2}$ est multiple de 3. -/
theorem number_theory_607174 (a b : ℤ) (h₀ : ¬ 3 ∣ a) (h₁ : ¬ 3 ∣ b) :
    3 ∣ a^4 - b^2 := by 
  -- If $k$ is not divisible by $3$, then $k ≡ 1$ or $2 (mod 3)$.
  have h_k_mod : ∀ k : ℤ, ¬ 3 ∣ k → k ≡ 1 [ZMOD 3] ∨ k ≡ 2 [ZMOD 3] := by
    intro k hk
    have : k % 3 ≠ 0 := by contrapose! hk; omega
    have : k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases this with h1 | h2
    · left
      exact Int.modEq_iff_add_fac.mpr ⟨-(k / 3), by
        have : k = 3 * (k / 3) + k % 3 := Eq.symm (Int.ediv_add_emod k 3)
        rw [h1] at this
        have : 1 = k - 3 * (k / 3) := by omega
        norm_num
        exact this⟩
    · right
      exact Int.modEq_iff_add_fac.mpr ⟨-(k / 3), by
        have : k = 3 * (k / 3) + k % 3 := Eq.symm (Int.ediv_add_emod k 3)
        rw [h2] at this
        have : 2 = k - 3 * (k / 3) := by omega
        norm_num
        exact this⟩

  -- If $k$ is not divisible by $3$, then $k^2 ≡ 1 (mod 3)$.
  have h_k_square_mod : ∀ k : ℤ, ¬ 3 ∣ k → k^2 ≡ 1 [ZMOD 3] := by
    intro k hk
    rcases h_k_mod k hk with h | h
    · have : k^2 ≡ 1^2 [ZMOD 3] := Int.ModEq.pow 2 h
      simp only [pow_one] at this
      exact this
    · have h_sq: k^2 ≡ 2^2 [ZMOD 3] := Int.ModEq.pow 2 h
      exact h_sq

  -- Prove $a^4 - b^2 ≡ 0 (mod 3)$.
  have h_main : a^4 - b^2 ≡ 0 [ZMOD 3] := by
    have h_a4: a^4 = (a^2)^2 := by rw [← pow_mul]
    have ha : a^2 ≡ 1 [ZMOD 3] := h_k_square_mod a h₀
    have hb : b^2 ≡ 1 [ZMOD 3] := h_k_square_mod b h₁
    have h_a4_mod: (a^2)^2 ≡ 1^2 [ZMOD 3] := Int.ModEq.pow 2 ha
    simp only [pow_one] at h_a4_mod
    have : a^4 - b^2 ≡ (a^2)^2 - b^2 [ZMOD 3] := by aesop
    have h_final_mod: (a^2)^2 - b^2 ≡ 1 - 1 [ZMOD 3] := Int.ModEq.sub h_a4_mod hb
    simp only [sub_self] at h_final_mod
    rw [h_a4]
    exact h_final_mod

  -- Prove $3 ∣ a^4 - b^2$.
  have h_final : 3 ∣ a^4 - b^2 := by
    rw [Int.dvd_iff_emod_eq_zero]
    tauto
  exact h_final
