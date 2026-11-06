import Mathlib

/-How many three-digit positive integers $x$ satisfy $3874x+481\equiv 1205 \pmod{23}$?-/
theorem number_theory_14989 : {x : ℕ | x ∈ Finset.Icc 100 999 ∧ (3874 * x + 481) ≡ 1205 [MOD 23]}.encard = 40 := by
  -- We begin by replacing the coefficients and constants in the equation with their residues modulo 23. We find that 3874 divided by 23 gives a remainder of 10, 481 divided by 23 gives a remainder of 21, and 1205 gives a remainder of 9. So the given congruence is equivalent to  $$
  -- 10x + 21 \equiv 9 \pmod{23}.
  -- $$Now add 2 to both sides to obtain $$
  -- 10x \equiv 11 \pmod{23}.
  -- $$Notice that we have replaced 23 with 0 on the left-hand side, since $23\equiv 0\pmod{23}$. Now let us find the modular inverse of 10. We want to find an integer which is divisible by 10 and one more than a multiple of 23. Note that since the units digit of 23 is 3, the units digit of $3\times 23$ is 9, so $3\times 23+1$ is a multiple of 10.  Thus $(3\times23+1)/10=7$ is the modular inverse of 10. Multiplying both sides of $10x \equiv 11 \pmod{23}$ by 7 gives $x\equiv 77 \pmod{23}$, which implies $x\equiv 8\pmod{23} $.
  have : {x : ℕ | x ∈ Finset.Icc 100 999 ∧ (3874 * x + 481) ≡ 1205 [MOD 23]} =
         {x : ℕ | x ∈ Finset.Icc 100 999 ∧ x ≡ 8 [MOD 23]} := by
    ext n
    simp
    intro hn hn'
    rw [Nat.ModEq, Nat.ModEq]
    simp
    omega
  rw [this]
  -- So the three digit solutions are  \begin{align*}
  -- 8+23\times 4 &= 100 \\
  -- 8+23\times 5 &= 123 \\
  -- &\vdots \\
  -- 8+23\times 43 &= 997,
  -- \end{align*}of which there are $\boxed{40}$.
  have : {x | x ∈ Finset.Icc 100 999 ∧ x ≡ 8 [MOD 23]}.encard =
         {x | x ∈ Finset.Icc 100 999 ∧ x ≡ 8 [MOD 23]}.ncard := by
    rw [Eq.comm, Set.Finite.cast_ncard_eq]
    have : ((Finset.Icc 100 999) : Set ℕ).Finite := by
      exact Finset.finite_toSet (Finset.Icc 100 999)
    apply Set.Finite.subset this
    apply Set.sep_subset
  rw [this]

  have : {x : ℕ | x ∈ Finset.Icc 100 999 ∧ x ≡ 8 [MOD 23]}.ncard = 40 := by
    apply Set.ncard_eq_of_bijective
    case f => exact fun i hi => 8 + 23 * (i + 4)
    simp
    intro a ha ha' ha''

    use (a - 8) / 23 - 4
    rw [Nat.ModEq] at ha''
    simp at ha''
    obtain ⟨k, hk⟩ := show 23 ∣ (a - 8) by omega
    rw [hk]
    simp
    omega

    intro i hi
    simp
    constructor
    . omega
    rw [Nat.ModEq]
    simp

    omega
  rw [this]
  simp
