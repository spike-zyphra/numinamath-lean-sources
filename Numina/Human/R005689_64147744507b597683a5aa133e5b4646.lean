import Mathlib

/- Lemma 1: ⟨a, 0⟩ ^ n = ⟨a ^ n, 0⟩ in ℤ√(-1) -/
lemma lemma_1 (a : ℤ) (n : ℕ) :
    (⟨a, 0⟩ : ℤ√(-1)) ^ n = ⟨a ^ n, 0⟩ := by
  -- Cast both sides to complex numbers
  apply GaussianInt.toComplex_injective
  -- Simplify both sides
  simp [GaussianInt.toComplex_def']

/- Lemma 2: ⟨0, b⟩ ^ n = ⟨0, (-1)^((n-1)/2) * b^n⟩ in ℤ√(-1) -/
lemma lemma_2 (b : ℤ) {n : ℕ} (hn : Odd n) :
    (⟨0, b⟩ : ℤ√(-1)) ^ n = ⟨0, (-1) ^ ((n - 1) / 2) * b ^ n⟩ := by
  -- Write n as 2k+1 for some k
  rcases hn with ⟨k, rfl⟩
  -- Cast both sides to complex numbers
  apply GaussianInt.toComplex_injective
  -- Simplify both sides
  simp [GaussianInt.toComplex_def']
  rw [mul_pow, pow_succ Complex.I, pow_mul, Complex.I_sq]
  ac_rfl

/- Lemma 3: ⟨a₁, b₁⟩ + n * ⟨a₂, b₂⟩ = ⟨a₁ + n * a₂, b₁ + n * b₂⟩ in ℤ√(-1) -/
lemma lemma_3 (a₁ a₂ b₁ b₂ : ℤ) (n : ℕ) :
    (⟨a₁, b₁⟩ : ℤ√(-1)) + n * (⟨a₂, b₂⟩ : ℤ√(-1)) = ⟨a₁ + n * a₂, b₁ + n * b₂⟩ := by
  -- Cast both sides to complex numbers
  apply GaussianInt.toComplex_injective
  -- Simplify both sides
  simp [GaussianInt.toComplex_def']
  ring

/- Let $z=a+b i$ be a complex number with integer real and imaginary parts $a, b \in \mathbb{Z}$, where $i=\sqrt{-1}$ (i.e. $z$ is a Gaussian integer). If $p$ is an odd prime number, show that the real part of $z^{p}-z$ is an integer divisible by $p$. -/
theorem number_theory_609419 (z : ℤ√(-1)) (p : ℕ) (hp : Nat.Prime p) (hp' : Odd p) :
    (p : ℤ) ∣ (z ^ p - z).re := by
  -- Write z as ⟨a, b⟩
  rcases z with ⟨a, b⟩
  -- We have p ∣ (x + y) ^ p - x ^ p - y ^ p in any ring.
  -- So we have ⟨a, b⟩ ^ p = ⟨a, 0⟩ ^ p + ⟨0, b⟩ ^ p + p * ⟨s, t⟩, for some s, t : ℤ
  rcases exists_add_pow_prime_eq hp (⟨a, 0⟩ : ℤ√(-1)) (⟨0, b⟩ : ℤ√(-1)) with ⟨⟨s, t⟩, h⟩
  simp at h ⊢
  -- Apply the lemmas
  simp [lemma_1, lemma_2, hp', lemma_3] at h
  -- Simplify the expression using `h`
  simp [h, ← ZMod.intCast_eq_intCast_iff_dvd_sub]
  -- Use Fermat's little theorem
  exact (@ZMod.pow_card _ ⟨hp⟩ _).symm
