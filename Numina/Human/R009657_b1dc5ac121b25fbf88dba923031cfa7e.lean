import Mathlib

/- The positive integers $a, b, c$ are pairwise relatively prime, $a$ and $c$ are odd and the numbers satisfy the equation $a^{2}+b^{2}=c^{2}$. Prove that $b+c$ is a square of an integer. -/
theorem number_theory_241496 (a b c : ℤ) (h : 0 < a) (h₀ : 0 < b) (h₁ : 0 < c)
    (h₂ : IsCoprime a b) (h₃ : IsCoprime b c) (h₄ : IsCoprime a c)
    (h₅ : Odd a) (h₆ : Odd c) (h₇ : a^2 + b^2 = c^2) :
    ∃ m, b + c = m^2 := by
    -- Since $a$ and $c$ are odd, $b$ must be even.
    have h₈ : Even b := by
      have h1 : Odd (a ^ 2) := by exact Odd.pow h₅
      have h2 : Odd (c ^ 2) := by exact Odd.pow h₆
      rw [← h₇] at h2
      apply (Int.odd_add.mp h2).mp at h1
      apply (Int.even_pow' (by simp)).mp h1
    -- We have $a^{2}=c^{2}-b^{2}=(c+b)(c-b)$.
    have h₉ : a ^ 2 = (c + b) * (c - b) := by
      ring_nf ;rw [← h₇] ;ring
    -- Let $d=\operatorname{gcd}(c+b, c-b)$.
    let d := Int.gcd (c + b) (c - b)
    -- Then $d$ divides $(c+b)+(c-b)=2 c$ and $(c+b)-(c-b)=2 b$.
    have h₁₀ : ↑d ∣ 2 * c := by
      have : 2 * c = (c + b) + (c - b) := by ring
      rw [this]
      apply Int.dvd_add Int.gcd_dvd_left Int.gcd_dvd_right
    have h₁₁ : ↑d ∣ 2 * b := by
      have : 2 * b = (c + b) - (c - b) := by ring
      rw [this]
      apply Int.dvd_sub Int.gcd_dvd_left Int.gcd_dvd_right
    -- Since $c+b$ and $c-b$ are odd, $d$ is odd,
    have h₁₂ : Odd d := by
      by_contra! ;simp at this ;rcases this with ⟨n, hn⟩
      have : (2:ℤ) ∣ d := by rw [hn,← two_mul] ;simp
      have this' : ↑d ∣ (c + b) := by exact Int.gcd_dvd_left
      have : (2:ℤ) ∣ (c + b) := by exact Int.dvd_trans this this'
      have : Even (c + b) := by exact (even_iff_exists_two_nsmul (c + b)).mpr this
      apply (Int.even_add.mp this).mpr at h₈
      have : ¬ Odd c := by exact Int.not_odd_iff_even.mpr h₈
      exact this h₆
    -- and hence $d$ divides both $b$ and $c$.
    have h₁₃ : Nat.Coprime d 2 := by exact Nat.coprime_two_right.mpr h₁₂
    have h₁₄ : ↑d ∣ b := by
      exact Int.dvd_of_dvd_mul_right_of_gcd_one h₁₁ h₁₃
    have h₁₅ : ↑d ∣ c := by
      exact Int.dvd_of_dvd_mul_right_of_gcd_one h₁₀ h₁₃
    -- But $b$ and $c$ are relatively prime, so $d=1$,
    have h₁₆ : d ∣ b.gcd c := by
      apply Nat.dvd_gcd
      exact Int.ofNat_dvd_left.mp h₁₄
      exact Int.ofNat_dvd_left.mp h₁₅
    have h₁₇ : b.gcd c = 1 := by exact Int.isCoprime_iff_gcd_eq_one.mp h₃
    rw [h₁₇] at h₁₆
    have h₁₈ : d = 1 := by exact Nat.dvd_one.mp h₁₆
    -- i.e., $c+b$ and $c-b$ are also relatively prime.
    have h₁₉ : IsCoprime (c + b) (c - b) := by
      exact Int.isCoprime_iff_gcd_eq_one.mpr h₁₈
    -- Since $(c+b)(c-b)=a^{2}$ is a square, it follows that $c+b$ and $c-b$ are also squares.
    symm at h₉
    apply (Int.sq_of_coprime h₁₉) at h₉
    rcases h₉ with ⟨t,h₉|h₉⟩
    use t ;simp [← h₉,add_comm]
    have : 0 < c + b := by exact Int.add_pos h₁ h₀
    rw [h₉] at this ;simp at this
    have : 0 ≤ t ^ 2 := by exact sq_nonneg t
    linarith