import Mathlib
/- Let $n$ be an integer. Prove that

$$
\left\lfloor\frac{n}{2}\right\rfloor+\left\lfloor\frac{n+1}{2}\right\rfloor=n .
$$ -/
theorem number_theory_611075 (n : ℤ) : ⌊(↑n : ℝ) / 2⌋ + ⌊((↑n : ℝ) + 1) / 2⌋ = n:= by
  -- We split the proof into two cases based on the remainder when n is divided by 2
  mod_cases n % 2
  -- Case 1: n is even (n % 2 = 0)
  .
    -- Replace the hypothesis with the statement that 2 divides n
    replace H : 2 ∣ n:= by exact Int.dvd_of_emod_eq_zero H
    -- Express n as 2k for some integer k
    replace H : ∃ k : ℤ, n = 2 * k:= by exact H
    -- Extract k from the existential statement
    rcases H with ⟨k, hk⟩
    -- Substitute n = 2k into the goal
    subst n
    -- Simplify expressions
    simp
    -- We need to prove that floor((2k + 1)/2) = k
    suffices ⌊(2 * (↑k : ℝ) + 1) / 2⌋ = k by linarith
    -- Apply the floor_eq_iff lemma to prove this
    refine Int.floor_eq_iff.mpr ⟨by linarith, by linarith⟩
  -- Case 2: n is odd (n % 2 = 1)
  .
    -- Replace the hypothesis with the statement that 2 divides (n - 1)
    replace H : 2 ∣ n - 1:= by exact Int.dvd_sub_of_emod_eq H
    -- Express (n - 1) as 2k for some integer k
    replace H : ∃ k : ℤ, n - 1 = 2 * k:= by exact H
    -- Extract k from the existential statement
    rcases H with ⟨k, hk⟩
    -- Rewrite n as 2k + 1
    replace hk : n = 2 * k + 1:= by linarith
    -- Substitute n = 2k + 1 into the goal
    subst n
    -- Simplify expressions
    simp
    -- Normalize ring expressions
    ring_nf
    -- Further simplification
    simp
    -- Simplify field expressions
    field_simp
    -- We need to prove that floor(1/2) = 0
    suffices ⌊(1 : ℝ) / 2⌋ = 0 by linarith
    -- Apply the floor_eq_iff lemma to prove this
    refine Int.floor_eq_iff.mpr ⟨(by simp), (by simp ; field_simp)⟩
