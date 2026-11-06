import Mathlib

set_option linter.dupNamespace false

/- Determine all positive integers $M$ for which the sequence $a_{0}, a_{1}, a_{2}, \ldots$, defined by $a_{0}=\frac{2 M+1}{2}$ and $a_{k+1}=a_{k}\left\lfloor a_{k}\right\rfloor$ for $k=0,1,2, \ldots$, contains at least one integer term. (Luxembourg) Answer. All integers $M \geqslant 2$. -/
namespace number_theory_24712

def a_from_M (M : ℕ) :=
  let rec a : ℕ → ℚ
  | 0 => (2 * M + 1) / 2
  | k + 1 => a k * ⌊a k⌋
  a

def ℤ_of_ℚ := Set.range ((↑·) : ℤ → ℚ)

theorem number_theory_24712 (M : ℕ) (M_pos : M > 0) :
    (∃ k, a_from_M M k ∈ ℤ_of_ℚ) ↔ M ≥ 2 := by
  let a := a_from_M M
  have a_fold : a_from_M.a M = a := rfl
  constructor
  . intro is_int
    by_cases M_eq : M = 1
    . by_contra
      have a_k_eq k : a k = 3 / 2 := by
        induction k with
        | zero =>
          unfold a a_from_M a_from_M.a
          rw [M_eq]
          norm_num
        | succ k ih =>
          unfold a a_from_M a_from_M.a
          rw [a_fold]
          rw [ih]
          norm_num
      have is_not_int : ∀ k, a k ∉ ℤ_of_ℚ := by
        intro _
        rw [a_k_eq]
        rintro ⟨n, _⟩
        have : n * 2 = 3 := by qify; linarith
        omega
      rcases is_int with ⟨k, k_is_int⟩
      exact is_not_int k k_is_int
    . omega
  . intro _
    have floor_a_k_even_implies_a_k_add_1_int k (M : ℤ) (M_even : 2 ∣ M) (a_k_eq : a k = M + 1 / 2) : a (k + 1) ∈ ℤ_of_ℚ := by
      unfold a a_from_M a_from_M.a
      rw [a_fold, a_k_eq]
      rw [(by norm_num : ⌊(M + 1 / 2 : ℚ)⌋ = M)]
      obtain ⟨half_M, M_eq⟩ := M_even
      rw [M_eq]
      norm_num
      ring_nf
      use half_M + half_M ^ 2 * 4
      simp
    by_cases 2 ∣ M
    . have a_0_eq : a 0 = M + 1 / 2 := by unfold a a_from_M a_from_M.a; ring
      have a_1_is_int : a 1 ∈ ℤ_of_ℚ := floor_a_k_even_implies_a_k_add_1_int 0 M (by omega) a_0_eq
      use 1
    by_cases M = 1
    . linarith
    . have : M ≥ 3 := by omega
      have : M % 2 = 1 := by omega
      obtain ⟨p, n₀, M_eq, n₀_odd⟩ : ∃ p n₀ : ℕ, M = 2 ^ p * n₀ + 1 ∧ n₀ % 2 = 1 := by
        rcases Nat.exists_eq_pow_mul_and_not_dvd (n := M - 1) (by omega) 2 (by simp) with ⟨p, n₀, M_odd, M_eq⟩
        use p, n₀
        omega
      have a_0_eq : a 0 = 2 ^ p * n₀ + 3 / 2 := by
        unfold a a_from_M a_from_M.a
        rw [M_eq]
        norm_num
        ring
      have a_k_eq_rec :
          ∀ (k : ℕ) (n_k : ℕ/-ℤ-/), n_k % 2 = 1 → ∀ p > 0, a k = 2 ^ p * n_k + 3 / 2 →
          ∃ n_k_add_1 : ℕ/-ℤ-/, n_k_add_1 % 2 = 1 ∧ a (k + 1) = 2 ^ (p - 1) * n_k_add_1 + 3 / 2 := by
        intro k n_k n_k_odd p p_gt_1 a_k_eq
        use 2 ^ (p + 1) * n_k ^ 2 + 5 * n_k
        constructor
        . calc
            2 ^ (p + 1) * n_k ^ 2 + 5 * n_k ≡ 0 + 1 [MOD 2] := by
              gcongr
              . ring_nf
                calc
                  n_k ^ 2 * 2 ^ p * 2 ≡ n_k ^ 2 * 2 ^ p * 0 [MOD 2] := by gcongr; rfl
                  _ = 0 := by simp
              . calc
                5 * n_k ≡ 1 * 1 [MOD 2] := by
                  gcongr
                  . rfl
                  . exact n_k_odd
                _ = 1 := by rfl
            _ = 1 := by rfl
        . unfold a a_from_M a_from_M.a
          rw [a_fold]
          rw [a_k_eq]
          have : ⌊(2 ^ p * n_k + 3 / 2 : ℚ)⌋ = 2 ^ p * n_k + 1 := by
            convert Int.floor_int_add (2 ^ p * n_k) (3 / 2 : ℚ)
            . norm_cast
            . norm_num
          rw [this]
          norm_num
          let p' := p - 1
          rw [show p = p' + 1 by omega]
          norm_num
          ring
      have : ∃ n_p : ℕ, a p = n_p + 3 / 2 ∧ 2 ∣ ⌊a p⌋ := by
        let rec rec_helper (k : ℕ) (n_k : ℕ/-ℤ-/) (n_k_odd : n_k % 2 = 1) p (a_k_eq : a k = 2 ^ p * n_k + 3 / 2) :
          ∃ n_k_add_p : ℕ/-ℤ-/, n_k_add_p % 2 = 1 ∧ a (k + p) = 2 ^ 0 * n_k_add_p + 3 / 2 := by
            match p with
            | 0 =>
              use n_k, n_k_odd
              exact a_k_eq
            | p' + 1 =>
              rcases a_k_eq_rec k n_k n_k_odd (p' + 1) (by simp) a_k_eq with ⟨n_k_add_1, n_k_add_1_odd, a_k_add_1_eq⟩
              have := rec_helper (k + 1) n_k_add_1 n_k_add_1_odd p' a_k_add_1_eq
              rw [show k + (p' + 1) = k + 1 + p' by ring]
              exact this
        rcases rec_helper 0 n₀ n₀_odd p a_0_eq with ⟨n_p, n_p_odd, a_p_eq⟩
        norm_num at a_p_eq
        use n_p
        constructor
        . exact a_p_eq
        . have : ⌊a p⌋ = n_p + 1 := by rw [a_p_eq]; norm_num
          omega
      use p + 1
      rcases this with ⟨n_p, a_p_eq, floor_a_p_even⟩
      have : a p = ⌊a p⌋ + 1 / 2 := by
        rw [a_p_eq]
        norm_num
        ring
      apply floor_a_k_even_implies_a_k_add_1_int p ⌊a p⌋ floor_a_p_even this

end number_theory_24712
