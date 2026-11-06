import Mathlib

/- Let $f(x)=x+5$ and let $g(x)=x^2+1$. Let $p(x)=g(x)+f(x)$ and let $q(x)=g(x)-f(x)$. Find $p(x)\cdot q(x)$. -/
theorem algebra_19515 {f g p q : ℝ → ℝ}
    (hf : f = fun x => x + 5) (hg : g = fun x => x ^ 2 + 1)
    (hp : p = fun x => g x + f x) (hq : q = fun x => g x - f x) :
    p * q = fun x => (x ^ 4 + x ^ 2 - 10 * x - 24) := by
  ext x
  simp [hp, hq, hf, hg]
  ring
