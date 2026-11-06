import Mathlib

theorem Number_Theory_n2 (b n : ℕ) (hb1 : 1 < b) (hb2 : 1 < n) (h : ∀ k : ℤ, 1 < k → ∃ a : ℤ, k ∣ (b - a^n)) :
    ∃ A : ℕ, b = A^n := by
  -- Let the prime factorization of $b$ be $b=p_{1}^{\alpha_{1}} \ldots p_{s}^{\alpha_{s}}$, where $p_{1}, \ldots, p_{s}$ are distinct primes.
  let α := b.factorization
  -- Our goal is to show that all exponents $\alpha_{i}$ are divisible by $n$, then we can set $A=p_{1}^{\alpha_{1} / n} \ldots p_{s}^{\alpha_{s} / n}$.
  suffices ∀ p ∈ α.support, n ∣ α p by
    let β := α.mapRange (fun p => p / n) (by simp)
    let A := β.prod (· ^ ·)
    use A
    have h1 : α = n • β := by
      ext p
      simp [β]
      rw [Nat.mul_div_cancel']
      by_cases hp : p ∈ α.support
      · apply this _ hp
      · simp at hp
        simp [hp]
    suffices b.factorization = (A ^ n).factorization by
      apply Nat.factorization_inj (by simp; omega) _ this
      simp
      intro h
      simp [h] at this
      rw [Nat.factorization_eq_zero_iff'] at this
      rcases this <;> omega
    simp
    convert h1
    simp [A]
    apply Nat.prod_pow_factorization_eq_self
    intro p hp
    replace hp : p ∈ α.support := by
      simp [β] at hp ⊢
      omega
    exact Nat.prime_of_mem_primeFactors hp
  -- Apply the condition for $k=b^{2}$.
  let k : ℤ := b^2
  obtain ⟨a_k, ha_k⟩ := h k (by simpa [k])
  -- The number $b-a_{k}^{n}$ is divisible by $b^{2}$ and hence, for each $1 \leq i \leq s$, it is divisible by $p_{i}^{2 \alpha_{i}}>p_{i}^{\alpha_{i}}$ as well.
  have h1 : ∀ p ∈ α.support, (p ^ (2 * α p) : ℤ) ∣ (b - a_k^n) := by
    intro p hp
    calc
      (p ^ (2 * α p) : ℤ) ∣ b^2 := by
        convert_to ((p ^ (α p)) ^ 2 : ℤ) ∣ b^2
        · apply pow_mul'
        rw [Int.pow_dvd_pow_iff]
        · convert_to ((p ^ (α p) : ℕ) : ℤ) ∣ (b : ℤ)
          · rw [Int.natCast_pow]
          rw [Int.ofNat_dvd]
          exact Nat.ordProj_dvd b p
        · norm_num
      _ ∣ _ := ha_k
  -- Therefore  $$ a_{k}^{n} \equiv b \equiv 0 \quad\left(\bmod p_{i}^{\alpha_{i}}\right) $$  and  $$ a_{k}^{n} \equiv b \not \equiv 0 \quad\left(\bmod p_{i}^{\alpha_{i}+1}\right) $$
  have h2 : ∀ p ∈ α.support, a_k^n ≡ 0 [ZMOD (p ^ (α p))] := by
    intro p hp
    specialize h1 p hp
    replace h1 : (p ^ (α p) : ℤ) ∣ (b - a_k^n) := by
      rw [pow_mul'] at h1
      calc
        _ ∣ (p ^ α p : ℤ) ^ 2 := by exact Dvd.intro_left ((p ^ α p : ℤ)^1) rfl
        _ ∣ _ := h1
    apply Int.ModEq.trans (b := b)
    · exact Int.modEq_iff_dvd.mpr h1
    suffices p ^ (α p) ∣ b by
      apply Dvd.dvd.modEq_zero_int
      rwa [← Int.natCast_pow, Int.ofNat_dvd]
    exact Nat.ordProj_dvd b p
  have h3 : ∀ p ∈ α.support, ¬ a_k^n ≡ 0 [ZMOD (p ^ (α p + 1))] := by
    intro p hp h
    specialize h1 p hp
    replace h1 : (p ^ (α p + 1) : ℤ) ∣ (b - a_k^n) := by
      calc
        _ ∣ (p ^ (2 * α p) : ℤ) := by
          rw [pow_dvd_pow_iff]
          · simp at hp
            omega
          · simp
            apply Nat.Prime.ne_zero
            exact Nat.prime_of_mem_primeFactors hp
          · rw [Int.ofNat_isUnit]
            simp
            apply Nat.Prime.ne_one
            exact Nat.prime_of_mem_primeFactors hp
        _ ∣ _ := h1
    rw [Int.modEq_zero_iff_dvd] at h
    have := Int.dvd_add h h1
    conv at this => rhs; ring_nf
    rw [← Int.natCast_pow, Int.ofNat_dvd] at this
    contrapose! this
    apply Nat.pow_succ_factorization_not_dvd (by omega)
    exact Nat.prime_of_mem_primeFactors hp
  -- which implies that the largest power of $p_{i}$ dividing $a_{k}^{n}$ is $p_{i}^{\alpha_{i}}$.
  have h4 : ∀ p ∈ α.support, multiplicity (p : ℤ) (a_k^n) = α p := by
    intro p hp
    specialize h2 p hp
    specialize h3 p hp
    rw [Int.modEq_zero_iff_dvd] at h2 h3
    observe : FiniteMultiplicity (↑p) (a_k ^ n)
    rw [← FiniteMultiplicity.multiplicity_lt_iff_not_dvd (by assumption)] at h3
    rw [FiniteMultiplicity.pow_dvd_iff_le_multiplicity (by assumption)] at h2
    omega
  -- Since $a_{k}^{n}$ is a complete $n$th power, this implies that $\alpha_{i}$ is divisible by $n$.
  intro p hp
  specialize h4 p hp
  rw [FiniteMultiplicity.multiplicity_pow] at h4
  · rw [← h4]
    apply Nat.dvd_mul_right
  · rw [← Nat.prime_iff_prime_int]
    exact Nat.prime_of_mem_primeFactors hp
  · rw [Int.finiteMultiplicity_iff_finiteMultiplicity_natAbs, Nat.finiteMultiplicity_iff]
    simp
    constructor
    · exact Nat.Prime.ne_one <| Nat.prime_of_mem_primeFactors hp
    intro ha_k'
    rw [ha_k', zero_pow (by omega)] at ha_k
    simp [k] at ha_k
    rw [← Int.natCast_pow, Int.ofNat_dvd] at ha_k
    exact Nat.not_pos_pow_dvd (a := b) (n := 2) (by assumption) (by norm_num) ha_k
