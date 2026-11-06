import Mathlib

open Nat

-- Example 1 Let $p$ be a prime number, and $m, n$ be non-negative integers. Find all triples $(p, m, n)$ that satisfy $p^{m}-n^{3}=8$.
theorem number_theory_323233 : {(p, m, n) : ℕ × ℕ × ℕ | p.Prime ∧ p ^ m - n ^ 3 = 8} = {(2, 3, 0), (3, 2, 1), (2, 4, 2)} := by
  ext ⟨p, m, n⟩
  conv_lhs => dsimp
  constructor
  . rintro ⟨p_prime, f_p_m_n_eq_8⟩
    -- Solve: From $p^{m}-n^{3}=8$, we know $$ p^{m}=(n+2)\left(n^{2}-2 n+4\right) \text {. } $$
    have : (n ^ 2 - 2 * n + 4 : ℤ) ≥ 0 := by
      nlinarith
    have toNat_eq : (n ^ 2 - 2 * n + 4 : ℤ).toNat = (n ^ 2 - 2 * n + 4 : ℤ) := by
      omega
    have p_pow_m_eq : p ^ m = (n + 2) * (n ^ 2 - 2 * n + 4 : ℤ).toNat := by
      zify
      rw [toNat_eq]
      zify at f_p_m_n_eq_8
      have : (↑(p ^ m - n ^ 3) : ℤ) = ↑(p ^ m) - ↑(n ^ 3) := by
        omega
      rw [this] at f_p_m_n_eq_8
      push_cast at f_p_m_n_eq_8
      linarith
    /-
    Since $p$ is a prime, without loss of generality, assume $$ p^{x}=n+2, p^{y}=n^{2}-2 n+4 \text {, } $$

    where $x, y \in \mathbf{Z}_{+}, x+y=m$.
    -/
    have p_ge_2 : p ≥ 2 := by
      exact Prime.two_le p_prime
    have : ∃ x ≤ m, n + 2 = p ^ x := by
      have : n + 2 ∣ p ^ m := by
        exact Dvd.intro _ p_pow_m_eq.symm
      exact (Nat.dvd_prime_pow p_prime).mp this
    rcases this with ⟨x, x_le_m, left_eq⟩
    have : ∃ y ≤ m, (n ^ 2 - 2 * n + 4 : ℤ).toNat = p ^ y :=
      (Nat.dvd_prime_pow p_prime).mp (Dvd.intro_left _ p_pow_m_eq.symm)
    rcases this with ⟨y, y_le_m, right_eq⟩
    have : x + y = m := by
      have p_pow_eq : p ^ x * p ^ y = p ^ m := by
        rw [←left_eq, ←right_eq]
        exact p_pow_m_eq.symm
      rw [show p ^ x * p ^ y = p ^ (x + y) by ring] at p_pow_eq
      exact Nat.pow_right_injective p_ge_2 p_pow_eq
    /-
    For any non-negative integer $n$, we have $$ \begin{array}{l} n^{2}-2 n+4-(n+2)=n^{2}-3 n+2 \ =(n-1)(n-2) \geqslant 0 . \end{array} $$

    Thus, $x \leqslant y$.
     -/
    have p_gt_1 : p > 1 := by
      exact Prime.one_lt p_prime
    have : x ≤ y := by
      have pow_le : p ^ x ≤ p ^ y := by
        rw [←left_eq, ←right_eq]
        zify
        rw [toNat_eq]
        suffices ((n - 1) * (n - 2) : ℤ) ≥ 0 by
          linarith
        by_cases (n : ℤ) ≤ 1
        . nlinarith
        . nlinarith
      exact (Nat.pow_le_pow_iff_right p_gt_1).mp pow_le
    --Therefore, $p^{x} \mid p^{y}$, i.e., $(n+2) \mid\left(n^{2}-2 n+4\right)$. Since $n^{2}-2 n+4=(n+2)^{2}-6(n+2)+12$, it follows that $(n+2) \mid 12$.
    have : p ^ x ∣ p ^ y := by
      exact (pow_dvd_pow_iff_le_right p_ge_2).mpr this
    have left_dvd_right : n + 2 ∣ (n ^ 2 - 2 * n + 4 : ℤ).toNat := by
      rw [left_eq, right_eq]
      exact this
    have : n + 2 ∣ 12 := by
      have right_eq_div_add_mod : (n ^ 2 - 2 * n + 4 : ℤ) = /- (n + 2) ^ 2 - 6 * (n + 2) + 12 -/ (n + 2) * (n - 4) + 12 := by
        ring
      have dvd_right : (n + 2 : ℤ) ∣ (n ^ 2 - 2 * n + 4 : ℤ) := by
        zify at left_dvd_right
        rw [toNat_eq] at left_dvd_right
        exact left_dvd_right
      zify
      rw [right_eq_div_add_mod] at dvd_right
      have dvd_mul : (n + 2 : ℤ) ∣ (n + 2) * (n - 4) := by
        exact Int.dvd_mul_right (↑n + 2) (↑n - 4)
      exact (Int.dvd_iff_dvd_of_dvd_add dvd_right).mp dvd_mul
    --Hence, $n+2 \in{2,3,4,6,12}$, i.e., $$ n \in{0,1,2,4,10} \text {. } $$
    have n_add_2_in : n + 2 ∈ Nat.divisors 12 :=
      mem_divisors.mpr ⟨this, by simp⟩
    have : Nat.divisors 12 = {1, 2, 3, 4, 6, 12} :=
      rfl
    rw [this] at n_add_2_in
    -- The curly brackets are needed here somehow.
    have n_in : n ∈ ({0, 1, 2, 4, 10} : Finset ℕ) := by
      generalize h : n + 2 = k
      rw [h] at n_add_2_in
      simp
      fin_cases n_add_2_in <;>
      . omega
    --When $n=0$, $p=2, m=3$; When $n=1$, $p=3, m=2$; When $n=2$, $p=2, m=4$; When $n=4$, $p^{m}=72=2^{3} \times 3^{2}$, which is impossible; When $n=10$, $p^{m}=1008=2^{4} \times 3^{2} \times 7$, which is impossible. In summary, the triples that satisfy the conditions are $$ (p, m, n)=(2,3,0),(3,2,1),(2,4,2) \text {. } $$
    --let primeFactors := ((n + 2) * (n ^ 2 - 2 * n + 4 : ℤ).toNat).primeFactors
    have := congrArg Nat.primeFactors p_pow_m_eq
    by_cases w_m_eq_0 : m = 0
    . simp [w_m_eq_0] at f_p_m_n_eq_8
      exfalso
      omega
    . have : (p ^ m).primeFactors = {p} := by
        exact primeFactors_prime_pow w_m_eq_0 p_prime
      have right_primeFactors_eq : ((n + 2) * (n ^ 2 - 2 * n + 4 : ℤ).toNat).primeFactors = {p} := by
        rw [p_pow_m_eq] at this
        exact this
      have right_primeFactors_card_eq_1 := congrArg Finset.card right_primeFactors_eq
      simp at this
      fin_cases n_in
      . dsimp at right_primeFactors_eq
        have : primeFactors 8 = {2} := by
          native_decide
        rw [this] at right_primeFactors_eq
        have : p = 2 := by
          simp at right_primeFactors_eq
          exact right_primeFactors_eq.symm
        rw [this]
        simp [this] at p_pow_m_eq
        have : m = 3 := by
          --rw [show 8 = 2 ^ 3 from rfl] at p_pow_m_eq
          exact Nat.pow_right_injective (by simp) p_pow_m_eq
        rw [this]
        decide
      . dsimp at right_primeFactors_eq
        have : primeFactors 9 = {3} := by
          native_decide
        rw [this] at right_primeFactors_eq
        have : p = 3 := by
          simp at right_primeFactors_eq
          exact right_primeFactors_eq.symm
        rw [this]
        simp [this] at p_pow_m_eq
        have : m = 2 := by
          exact Nat.pow_right_injective (by simp) p_pow_m_eq
        rw [this]
        decide
      . dsimp at right_primeFactors_eq
        have : primeFactors 16 = {2} := by
          native_decide
        rw [this] at right_primeFactors_eq
        have : p = 2 := by
          simp at right_primeFactors_eq
          exact right_primeFactors_eq.symm
        rw [this]
        simp [this] at p_pow_m_eq
        have : m = 4 := by
          exact Nat.pow_right_injective (by simp) p_pow_m_eq
        rw [this]
        decide
      . dsimp at right_primeFactors_card_eq_1
        have : primeFactors 72 = {2, 3} := by
          native_decide
        simp [this] at right_primeFactors_card_eq_1
      . dsimp at right_primeFactors_card_eq_1
        have : primeFactors 1008 = {2, 3, 7} := by
          native_decide
        simp [this] at right_primeFactors_card_eq_1
  . intro p_m_n_in
    --generalize h : (p, m, n) = x
    --rw [h] at p_m_n_in
    rw [show ({(2, 3, 0), (3, 2, 1), (2, 4, 2)} : Set (ℕ × ℕ × ℕ)) = ({(2, 3, 0), (3, 2, 1), (2, 4, 2)} : Finset (ℕ × ℕ × ℕ)) by simp] at p_m_n_in
    norm_cast at p_m_n_in
    fin_cases p_m_n_in <;>
    . decide
