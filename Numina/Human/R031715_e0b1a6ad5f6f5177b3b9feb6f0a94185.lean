import Mathlib

/- 4. It is known that $a$ is an odd integer, and $x_{1}$ and $x_{2}$ are the roots of the equation $x^{2} + a x - 1 = 0$. Prove that for any integer $n \geq 0$, the numbers $x_{1}^{n} + x_{2}^{n}$ and $x_{1}^{n+1} + x_{2}^{n+1}$ are integers and coprime. -/
theorem number_theory_194071 (a : ℤ) (ha : Odd a) (x₁ x₂ : ℝ)
    (hroots : ∀ x : ℝ, x^2 + a * x - 1 = 0 ↔ x = x₁ ∨ x = x₂) :
    ∀ n : ℕ, ∃ m₁ m₂ : ℤ, x₁ ^ n + x₂ ^ n = m₁ ∧ x₁ ^ (n + 1) + x₂ ^ (n + 1) = m₂ ∧
    IsCoprime m₁ m₂ := by
  -- Show that x₁ + x₂ = -a and x₁ * x₂ = -1
  have ⟨hadd, hmul⟩ : x₁ + x₂ = -a ∧ x₁ * x₂ = -1 := by
    simp_rw [show ∀ x : ℝ, x^2 + a * x - 1 = x * x - (-a) * x + (-1) by intros; ring] at hroots
    have eq : x₁ * x₁ - (-a) * x₁ + (-1) = 0 := by simp only [hroots, true_or]
    -- x₁ is a root of x^2 + a * x - 1 = 0.
    -- Vieta's formula for the quadratic equation x^2 + a * x - 1 = 0 implies that
    -- there exists y such that y^2 + a * x - 1 = 0 and x₁ + y = -a, x₁ * y = -1.
    have ⟨y, hy, hadd, hmul⟩ := vieta_formula_quadratic eq
    -- It is enough to show that y ≠ x₁.
    suffices y ≠ x₁ by
      -- If y ≠ x₁ then y = x₂ (because any root of x^2 + a * x - 1 = 0 is either x₁ or x₂).
      cases' (hroots y).mp hy with hy hy
      · contradiction
      -- y = x₂ implies that x₁ + x₂ = -a and x₁ * x₂ = -1.
      · subst y
        exact ⟨hadd, hmul⟩
    -- Show that y ≠ x1. Suppose that y = x₁ then x₁ * y = x₁^2 = -1, a contradiction.
    contrapose! hmul
    nlinarith
  -- Define s(n) = x₁^n + x₂^n.
  set s : ℕ → ℝ := fun n => x₁ ^ n + x₂ ^ n
  -- Show that s(k + 2) = s(k) - a * s(k + 1).
  have hs k : s (k + 2) = s k - a * s (k + 1) := by
    -- The result follows from the definition of s(n):
    -- s(k + 2) = x₁^(k + 2) + x₂^(k + 2) = (x₁ + x₂) * (x₁^(k + 1) + x₂^(k + 1)) - x₁ * x₂ * (x₁^k + x₂^k)
    --          = -a * s(k + 1) + s(k) (because x₁ + x₂ = -a and x₁ * x₂ = -1).
    rw [show s k = -(-1 * s k) by ring, show a * s (k + 1) = -(-a * s (k + 1)) by ring]
    rw [← hmul, ← hadd]
    simp_rw [s]
    ring_nf
  intro n
  -- Prove the main result by induction on n.
  induction n with
  | zero =>
    -- If n = 0 then show that s(0) = 2, s(1) = -a and s(0) and s(1) are coprime.
    -- s(0) = x₁^0 + x₂^0 = 2, s(1) = x₁ + x₂ = -a.
    use 2, -a
    norm_num [hadd]
    -- We need to show that 2 and -a are coprime.
    rw [Int.coprime_iff_nat_coprime]
    -- We know that a is odd so 2 and |-a| = a are coprime.
    -- It follows that 2 and -a are coprime also.
    apply Odd.coprime_two_left
    rw [Int.natAbs_neg]
    exact Odd.natAbs ha
  | succ n ih =>
    -- Consider n + 1.
    -- The induction hypothesis implies that s(n) = p ∈ ℤ, s(n + 1) = q ∈ ℤ, and
    -- u * p + v * q = 1 for some u, v ∈ ℤ (since p and q are coprime).
    have ⟨p, q, hp, hq, ⟨u, v, h⟩⟩ := ih
    -- Take m₁ = q and m₂ = p - a * q.
    use q, p - a * q
    -- We have s(n + 2) = s(n) - a * s(n + 1) = p - a * q ∈ ℤ.
    simp [hq, add_assoc, show x₁ ^ (n + 2) + x₂ ^ (n + 2) = s (n + 2) by simp [s], hs]
    simp [s, hp, hq]
    -- Show that q and p - a * q are coprime.
    -- We have (v + u * a) * q + u * (p - a * q) = v * q + u * p = 1, so
    -- q and p - a * q are coprime.
    use v + u * a, u
    linear_combination h