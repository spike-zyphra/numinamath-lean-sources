import Mathlib

set_option linter.dupNamespace false

namespace number_theory_605030

def a_from_m (m : ℕ) :=
  let rec a : ℕ → ℚ
  | 0 => (2 * m + 1) / 2
  | k + 1 => a k * ⌊a k⌋
  a

def ℤ_of_ℚ := Set.range ((↑·) : ℤ → ℚ)

/- Man bestimme alle positiven ganzen Zahlen $m$ mit folgender Eigenschaft:
Die Folge $a_{0}, a_{1}, a_{2}, \ldots$ mit $a_{0}=\frac{2 m+1}{2}$ und $a_{k+1}=a_{k}\left\lfloor a_{k}\right\rfloor$ für $k=0,1,2, \ldots$ enthält wenigstens eine ganze Zahl.
Hinweis: $\lfloor x\rfloor$ bezeichnet den größten ganzen Teil (integer-Funktion) von $x$. -/
theorem number_theory_605030 (m : ℕ) :
    m > 0 →
    (
      (
        let a := a_from_m m
        ∃ k, a k ∈ ℤ_of_ℚ
      ) ↔ m ≠ 1
    ) := by
  intro m_pos
  let a := a_from_m m
  --have a_unfold : a = a_from_m.a m := rfl
  have a_fold : a_from_m.a m = a := rfl
  constructor
  . intro is_int
    by_cases m_eq : m = 1
    . -- Furthermore, for $m=1$, we have $a_{0}=\frac{3}{2},\left\lfloor a_{0}\right\rfloor=1$, and for $a_{k}=\frac{3}{2}$, it always follows that $a_{k+1}=\frac{3}{2} \cdot 1=\frac{3}{2}$. Thus, there is no integer term in the sequence.
      by_contra
      have a_k_eq k : a k = 3 / 2 := by
        induction k with
        | zero => unfold a a_from_m a_from_m.a
                  rw [m_eq]
                  norm_num
        | succ k ih => unfold a a_from_m a_from_m.a
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
    . assumption
  . intro _
    have floor_a_k_even_implies_a_k_add_1_int k (m : ℤ) (m_even : 2 ∣ m) (a_k_eq : a k = m + 1 / 2) : a (k + 1) ∈ ℤ_of_ℚ := by
      unfold a a_from_m a_from_m.a
      rw [a_fold, a_k_eq]
      rw [(by norm_num : ⌊(m + 1 / 2 : ℚ)⌋ = m)]
      obtain ⟨half_m, m_eq⟩ := m_even
      rw [m_eq]
      norm_num
      ring_nf
      use half_m + half_m ^ 2 * 4
      simp
    --have floor_add_half_eq {z : ℤ} : ⌊(z + 1 / 2 : ℚ)⌋ = z := by norm_num --by convert Int.floor_int_add z (1 / 2 : ℚ); norm_num
    by_cases /-whether_m_even :-/ 2 ∣ m
    . -- It holds that $a_{0}=m+\frac{1}{2}$ and $a_{1}=a_{0}\left\lfloor a_{0}\right\rfloor=\left(m+\frac{1}{2}\right) \cdot m=m^{2}+\frac{m}{2}$.
      have a_0_eq : a 0 = m + 1 / 2 := by unfold a a_from_m a_from_m.a; ring
      /- generalized above and not needed anymore
      have a_1_eq : a 1 = m ^ 2 + m / 2 := by
        unfold a a_from_m a_from_m.a
        rw [a_fold, a_0_eq]
        rw [(by norm_num : ⌊(m + 1 / 2 : ℚ)⌋ = m)]
        norm_num
        ring
      -/
      -- This expression is obviously an integer for even $m$, so the desired property of the sequence is present here.
      have a_1_is_int : a 1 ∈ ℤ_of_ℚ := floor_a_k_even_implies_a_k_add_1_int 0 m (by omega) a_0_eq
      use 1
    by_cases m = 1
    . contradiction
    . -- Now let $m \geq 3$ be odd.
      have : m ≥ 3 := by omega
      have /-m_odd-/ : m % 2 = 1 := by omega
      -- There exists a unique representation $m=2^{p} \cdot n_{0}+1$ with $p \geq 1, n_{0}$ odd and $p, n_{0} \in \mathbb{N}$.
      obtain ⟨p, n₀, m_eq, n₀_odd⟩ : ∃ p n₀ : ℕ, m = 2 ^ p * n₀ + 1 ∧ n₀ % 2 = 1 := by
        rcases Nat.exists_eq_pow_mul_and_not_dvd (n := m - 1) (by omega) 2 (by simp) with ⟨p, n₀, m_odd, m_eq⟩
        use p, n₀
        omega
      /-
      Thus, $a_{0}=2^{p} n_{0}+\frac{3}{2}$,
      and for $a_{k}=2^{p} n_{k}+\frac{3}{2}$ ( $n_{k}$ odd),
      it follows that $a_{k+1}=\left(2^{p} n_{k}+\frac{3}{2}\right)\left(2^{p} n_{k}+1\right)=2^{p-1}\left(2^{p+1} n_{k}^{2}+5 n_{k}\right)+\frac{3}{2}$, where the term in parentheses is odd.
      Therefore, there exists a representation $a_{k+1}=2^{p-1} n_{k+1}+\frac{3}{2}$ with odd $n_{k+1}$.
      -/
      have a_0_eq : a 0 = 2 ^ p * n₀ + 3 / 2 := by
        unfold a a_from_m a_from_m.a
        rw [m_eq]
        norm_num
        ring
      -- Don't omit `n_k : ℕ` here otherwise it's inferred to be `ℚ`.
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
        . unfold a a_from_m a_from_m.a
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
      -- By increasing $k$ by 1, $p$ is simultaneously decreased by 1, so that $a_{k+p}=2^{0} n_{k+p}+\frac{3}{2}$ holds and $\left\lfloor a_{k+p}\right\rfloor$ is even.
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
      -- Then $a_{k+p+1}$ is an integer, and thus the desired property of the sequence is also present for every $m \geq 3$.
      use p + 1
      rcases this with ⟨n_p, a_p_eq, floor_a_p_even⟩
      have : a p = ⌊a p⌋ + 1 / 2 := by
        rw [a_p_eq]
        norm_num
        ring
      apply floor_a_k_even_implies_a_k_add_1_int p ⌊a p⌋ floor_a_p_even this
    -- Therefore, all positive integers except 1 belong to the desired set.

end number_theory_605030
