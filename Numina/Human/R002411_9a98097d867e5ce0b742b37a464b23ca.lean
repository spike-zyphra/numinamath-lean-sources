import Mathlib

open Complex Set

/- For how many positive integers $n$ less than or equal to $1000$ is $(\sin t + i \cos t)^n = \sin nt + i \cos nt$ true for all real $t$? -/
theorem algebra_92981 :
  {n : ℕ | 0 < n ∧ n ≤ 1000 ∧ ∀ t : ℝ, (sin t + I * cos t)^n = sin (n * t) + I * cos (n * t)}.ncard = 250
:= by
  -- Let the set of all such $n$ be $S$.
  generalize hS : {n : ℕ | 0 < n ∧ n ≤ 1000 ∧ ∀ t : ℝ, (sin t + I * cos t)^n = sin (n * t) + I * cos (n * t)} = S

  -- We claim that $S$ is the set of all integers between $0$ and $1000$ that are equivalent to 1 mod 4.
  let f x := x * 4 + 1
  have hS' : S = f '' Set.Icc 0 249 := by
    ext x
    constructor
    -- Here we show that if $x$ is in $S$, then x is equivalent to 1 mod 4.
    · intro hx
      rw [<-hS] at hx
      simp at *
      rcases hx with ⟨ hl, hr, hx ⟩
      specialize hx 0
      simp at *
      have dalg : ∃ k r, x = 4 * k + r ∧ r < 4 := by
        exists x / 4, x % 4
        constructor
        · apply Eq.symm (Nat.div_add_mod _ _)
        · apply Nat.mod_lt
          simp
      rcases dalg with ⟨ k, r, hx', hrem ⟩
      rw [hx', pow_add, pow_mul, Complex.I_pow_four, one_pow, one_mul] at hx
      have hrem' : r = 1 := by
        rcases r with r | r | r | r | r
        · apply (congr_arg Complex.re) at hx
          simp at *
        · apply (congr_arg Complex.re) at hx
          simp at *
        · apply (congr_arg Complex.re) at hx
          simp at *
        · simp [pow_three, Complex.I_mul_I] at *
          apply (congr_arg Complex.im) at hx
          simp at *
          linarith
        · linarith
      replace hx := hx'
      cases hrem'
      clear hrem hx'
      rw [hx]
      unfold f
      exists k
      constructor
      · linarith
      · linarith
    -- Here we show that if then x is equivalent to 1 mod 4, then $x$ is in $S$.
    · intro hx
      unfold f at hx
      rw [<-hS]
      simp at *
      rcases hx with ⟨ k, hk, hkx ⟩
      constructor <;> try constructor
      · linarith
      · linarith
      · intro t
        have rotate : (sin t + I * cos t) = I * (cos (-t) + sin (-t) * I) := by
          ring_nf
          rw [Complex.I_sq]
          simp
          ring_nf
        rw [rotate, mul_pow]
        clear rotate
        have rotate : sin (x * t) + I * cos (x * t) = I * (cos (- x * t) + sin (- x * t) * I) := by
          ring_nf
          rw [Complex.I_sq]
          simp
          ring_nf
        rw [rotate]
        rw [Complex.cos_add_sin_mul_I_pow]
        congr 1
        · rw [<- hkx]
          simp [pow_add, pow_mul', Complex.I_pow_four]
        · simp

  -- Therefore, the size of S is the size of the set of all integers between $0$ and $1000$ that are equivalent to 1 mod 4.
  rw [hS']
  have hf : f.Injective := by
    intro x y h
    linarith
  rw [Set.ncard_image_of_injective _ hf]
  simp [<- Set.Nat.card_coe_set_eq]