import Mathlib

-- A set \( A \) of integers is said to be admissible if it satisfies the following property: for all \( x, y \in A \) (not necessarily distinct), and for every \( k \in \mathbb{Z} \), we have \( x^2 + kxy + y^2 \in A \). Determine all pairs of non-zero integers \( (m, n) \) such that the only admissible set containing both \( m \) and \( n \) is \( \mathbb{Z} \).
theorem number_theory_607377 (m n:ℤ)(A : Set ℤ)(hm : m ∈ A)(hn : n ∈ A)(hA : ∀ (x y k :ℤ), x ∈ A ∧ y ∈ A → x^2+k*x*y+y^2 ∈ A) : (Int.gcd m n = 1 → A = ⊤) ∧ (gcd m n > 1 → ∃ A':Set ℤ, m ∈ A' ∧ n ∈ A' ∧ (∀ (x y k :ℤ), x ∈ A' ∧ y ∈ A' → x^2+k*x*y+y^2 ∈ A') ∧ A' < ⊤):= by
  constructor
  · -- Conversely, let \\( m \\) and \\( n \\) be integers such that \\(\\gcd(m, n) = 1\\). We will show that any admissible set containing \\( m \\) and \\( n \\) must be equal to \\( \\mathbb{Z} \\).
    intro hgcd
    -- Let \\( A \\) be an admissible set containing \\( m \\) and \\( n \\). Notice that if \\( x \\in A \\), then by the hypothesis, for any integer \\( k \\), the integer$ x^2 + k \\cdot x \\cdot x + x^2 = (k + 2) x^2 $ is in \\( A \\). Hence, all multiples of \\( x^2 \\) belong to \\( A \\) whenever \\( x \\in A \\).
    have hpow : ∀ x, x ∈ A → ∀ k, x^2 * k ∈ A := by
      intro x hx k
      have := hA x x (k-2) ⟨hx, hx⟩
      group at this
      exact this
    -- Note that if \\(\\gcd(m, n) = 1\\), then also \\(\\gcd(m^2, n^2) = 1\\)
    have hgcdpow : Int.gcd (m^2) (n^2) = 1 := by
      have hmnat: (m^2).natAbs = m.natAbs^2 := by exact Int.natAbs_pow m 2
      have hnnat: (n^2).natAbs = n.natAbs^2 := by exact Int.natAbs_pow n 2
      have : Nat.gcd (m.natAbs) (n.natAbs) = 1 := hgcd
      have : Nat.gcd (m.natAbs^2) (n.natAbs^2) = 1 := by
        exact Nat.Coprime.pow 2 2 hgcd
      apply @Tactic.NormNum.int_gcd_helper (m^2) (n^2) (m.natAbs ^ 2) (n.natAbs ^ 2) 1 hmnat hnnat this
    -- By Bézout's theorem, there exist integers \\( u, v \\in \\mathbb{Z} \\) such that
    have : ∃ u v, 1 = m^2*u+n^2*v := by
      have := Int.gcd_eq_gcd_ab (m^2) (n^2)
      rw [hgcdpow] at this
      use (m ^ 2).gcdA (n ^ 2)
      use (m ^ 2).gcdB (n ^ 2)
      exact this
    rcases this with ⟨u, v, huv⟩
    -- Since \\( u m^2 \\) and \\( v n^2 \\) are in \\( A \\)
    have hu : m^2 * u ∈ A := by apply hpow m hm
    have hv : n^2 * v ∈ A := by apply hpow n hn
    -- applying the hypothesis to \\( x = u m^2 \\), \\( y = v n^2 \\), and \\( k = 2 \\), we get $ (u m^2)^2 + 2 u m^2 \\cdot v n^2 + (v n^2)^2 = (u m^2 + v n^2)^2 = 1
    have := hA (m^2*u) (n^2*v) 2 ⟨hu, hv⟩
    group at this
    have heq : 1 = m ^ 2 * u * n ^ 2 * v * 2 + m ^ 4 * u ^ 2 + n ^ 4 * v ^ 2 := by
      rw [← one_pow 2, huv]
      group
    rw [← heq] at this
    -- Therefore, for all \\( k \\in \\mathbb{Z} \\), \\( k \\cdot 1^2 = k \\in A \\). Thus, \\( A = \\mathbb{Z} \\), and the only admissible set containing \\( m \\) and \\( n \\) is \\( \\mathbb{Z} \\).
    ext x
    constructor
    · exact fun a => trivial
    · intro hx
      have := hpow 1 this x
      simp at this
      exact this
  · --Note that if \\( d = \\gcd(m, n) &gt; 1 \\), then the set \\( A \\) of multiples of \\( d \\) is an admissible set containing both \\( m \\) and \\( n \\), but \\( A \\) is not equal to ℤ
    intro hgcd
    let A' := {x | gcd m n ∣ x}
    use A'
    constructor
    -- Indeed, if \\( x \\) and \\( y \\) are multiples of \\( d \\), then for any integer \\( k \\), the number $x²+kxy+y²$ is divisible by \\( d \\) and thus belongs to A
    · show gcd m n ∣ m
      exact gcd_dvd_left m n
    · constructor
      · show gcd m n ∣ n
        exact gcd_dvd_right m n
      · constructor
        · intro x y k ⟨hx, hy⟩
          have hx : gcd m n ∣ x := hx
          have hy : gcd m n ∣ y := hy
          show gcd m n ∣ x^2+k*x*y+y^2
          apply Int.dvd_add
          · apply Int.dvd_add
            · apply dvd_pow hx (by norm_num)
            · apply Dvd.dvd.mul_left hy (k * x)
          · apply dvd_pow hy (by norm_num)
        · unfold A'
          simp
          apply (Set.ssubset_iff_of_subset fun ⦃a⦄ a => trivial).mpr
          use 1
          constructor
          · exact trivial
          · simp
            intro hgcd'
            have := @Int.eq_one_of_dvd_one (gcd m n) (by linarith) hgcd'
            linarith
