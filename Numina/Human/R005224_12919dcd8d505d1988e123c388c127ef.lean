import Mathlib

open Real

/- Determine all functions $f: \mathbb{R} \rightarrow \mathbb{R}$ such that  $$ f\left(x^{2}-y^{2}\right)=x f(x)-y f(y) $$  for all pairs of real numbers $x$ and $y$. -/
theorem algebra_606348 (f : ℝ → ℝ) : (∀ x y, f (x ^ 2 - y ^ 2) = x * f x - y * f y) ↔
∃ c, ∀ x, f x = c * x := by
  constructor
-- Plug in $x=y=0$ to feq to get $f(0)=0$
  · intro feq; have f0 : f 0 = 0 := by
      specialize feq 0 0; simp at feq; exact feq
  -- Plug in $y=0$ to feq to get $f(x)=x*f(x)$
    have fx1 : ∀ x, f (x ^ 2) = x * f x := by
      intro x; specialize feq x 0; simp at feq; exact feq
  -- Plug in $x=0$, $y=√x$ (or $y=√-x$) to feq to show that $f$ is an odd function
    have fodd : ∀ x, f (-x) = -f x := by
      have : ∀ x ≥ 0, f (-x) = -f x := by
        intro x hx; have : x = (√x) ^ 2 := by rw [pow_two]; symm; exact mul_self_sqrt hx
        specialize feq 0 √x; simp at feq; rw [← fx1, ← this] at feq; exact feq
      intro x; by_cases h : 0 ≤ x; exact this x (show _ by linarith)
      specialize this (-x) (show _ by linarith); simp at this; simp [this]
  -- Prove that $f$ is additive
    have fadd : ∀ x y, f (x + y) = f x + f y := by
      intro x y; wlog h : 0 ≤ x + y
      · specialize this f feq f0 fx1 fodd (-x) (-y) (show _ by linarith)
        rw [show -x+-y = -(x+y) by ring] at this; simp only [fodd] at this
        rw [neg_eq_iff_eq_neg] at this; rw [this]; ring
      wlog h' : x ≤ y
      · specialize this f feq f0 fx1 fodd y x (show _ by linarith) (show _ by linarith)
        rw [add_comm, this, add_comm]
      replace h' : 0 ≤ y := by linarith
      rw [← mul_self_sqrt h, ← pow_two, fx1, ← sub_eq_iff_eq_add]
      nth_rw 3 [← mul_self_sqrt h']; rw [← pow_two, fx1, ← feq, pow_two, pow_two]
      rw [mul_self_sqrt h', mul_self_sqrt h]; simp
  -- Fulfill the final goal with $f(1)$ and specialize fx1 at $x+1$, then use fadd to simplify and prove the final goal
    use f 1; intro x; have := fx1 (x+1); ring_nf at this
    simp [fadd, mul_two, fx1, ← sub_eq_zero] at this; ring_nf at this
    rw [neg_add_eq_zero] at this; rw [this]
-- Conversely, it is straightforward to check that if $f(x)=c*x$ for some $c$, the functional equation in question holds
  rintro ⟨c, hc⟩; intros; simp [hc]; ring