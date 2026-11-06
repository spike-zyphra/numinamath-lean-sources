import Mathlib

/- Consider all functions $f: \mathbb{Z} \rightarrow \mathbb{Z}$ satisfying

$$
f(f(x)+2 x+20)=15
$$

Call an integer $n$ good if $f(n)$ can take any integer value. In other words, if we fix $n$, for any integer $m$, there exists a function $f$ such that $f(n)=m$. Find the sum of all good integers $x$. -/
theorem algebra_609436 :
    ∑ᶠ (n : ℤ) (_ : ∀ m, ∃ f : ℤ → ℤ, (∀ x, f (f x + 2 * x + 20) = 15) ∧ f n = m), n = -35 := by
  -- It suffices to show that the only good integer is 35
  suffices hn : ∀ n, (∀ m, ∃ f : ℤ → ℤ, (∀ x, f (f x + 2 * x + 20) = 15) ∧ f n = m) ↔ n = -35 by simp [hn]
  intro n
  constructor
  . -- We show that any good integer n must be 35
    -- For almost all integers n, f(n) ≠ -n-20
    -- If f(n) = -n-20, then f(n) = f(f(n) + 2n + 20) = 15
    -- So n must be 35
    intro h
    obtain ⟨f, h₁, h₂⟩ := h (-n - 20)
    specialize h₁ n
    rw [h₂] at h₁
    ring_nf at h₁
    linarith
  . -- We show that 35 is good
    rintro rfl
    -- We take the function f(x) = m if x = -35, and f(x) = 15 otherwise
    intro m
    use fun x ↦ if x = -35 then m else 15
    -- Verify that f satisfies the condition
    simp
    intro x h
    split_ifs at h with hx
    . linarith
    . absurd hx
      linarith only [h]
