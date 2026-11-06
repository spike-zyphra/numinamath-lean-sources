import Mathlib

/- Let $*$ denote an operation, assigning a real number $a * b$ to each pair of real numbers ( $a, b)$ (e.g., $a * b=$ $a+b^{2}-17$ ).
  Devise an equation which is true (for all possible values of variables) provided the operation $*$ is commutative or associative and which can be false otherwise. -/
theorem algebra_236980 :
  (∀ f : ℝ → ℝ → ℝ, (∀ a b, f a b = f b a) → ∀ a ,f a (f a a) = f (f a a) a) ∧
  (∀ f : ℝ → ℝ → ℝ, (∀ a b c, f (f a b) c = f a (f b c)) → ∀ a,f a (f a a) = f (f a a) a) ∧
  (∃ f : ℝ → ℝ → ℝ, ¬ (∀ a b, f a b = f b a) ∧ ¬ (∀ a b c, f (f a b) c = f a (f b c)) ∧ ¬ (∀ a,f a (f a a) = f (f a a) a)) := by
  -- A suitable equation is $x *(x \* x)=(x \* x) \* x$
  -- which is obviously true if $*$ is any commutative or associative operation
  constructor
  · intro f hf a
    rw [hf]
  constructor
  · intro f hf a
    rw [hf]
  -- but does not hold in general, e.g., $1-(1-1) \neq(1-1)-1$.
  use (fun a b => a - b)
  constructor
  · simp ;use 1, 2 ;norm_num
  constructor
  · simp ;use 1, 1, 1 ;norm_num
  simp ;use 1 ;norm_num
  