import Mathlib

/- Let $f: \mathbb{Z} \rightarrow \mathbb{Z}$ be a function satisfying $f(0) \neq 0, f(1)=0$ and

(i) $f(x y)+f(x) f(y)=f(x)+f(y)$;

(ii) $(f(x-y)-f(0)) f(x) f(y)=0$,

for all $x, y \in \mathbb{Z}$, simultaneously.

(a) Find the set of all possible values of the function $f$.

(b) If $f(10) \neq 0$ and $f(2)=0$, find the set of all integers $n$ such that $f(n) \neq 0$. -/
theorem algebra_607861 {f : ℤ → ℤ} (h0 : f 0 ≠ 0) (h1 : f 1 = 0)
  (h2 : ∀ x y, f (x * y) + f x * f y = f x + f y)
  (h3 : ∀ x y, (f (x - y) - f 0) * f x * f y = 0) :
  (∀ x, f x = 0 ∨ f x = 1) ∧ (f 10 ≠ 0 → f 2 = 0 → {x | f x ≠ 0} = {x | 5 ∣ x}):= by
    -- $$ (f(x)-f(0)) f(x)=0 $$

    -- for all $x$ (since $f(0) \neq 0$ ). Thus either $f(x)=0$ or $f(x)=f(0)$, for all $x \in \mathbb{Z}$.
    have proofa : ∀ x, f x = 0 ∨ f x = 1 := by
      intro x
      
      specialize h3 x 0
      simp [h0] at h3
      rcases h3 with h3 | h3
      · 
        -- Now taking $x=y=0$ in (i), we see that $f(0)+f(0)^{2}=2 f(0)$. This shows that $f(0)=0$ or $f(0)=1$. Since $f(0) \neq 0$, we must have $f(0)=1$. We conclude that
        -- $$ \text { either } f(x)=0 \text { or } f(x)=1 \text { for each } x \in \mathbb{Z} $$
        -- This shows that the set of all possible value of $f(x)$ is ${0,1}$. This completes (a).
        specialize h2 0 0
        simp at h2
        nth_rw 3 [←mul_one (f 0)] at h2
        rw [Int.mul_eq_mul_left_iff h0] at h2
        simp [h2] at h3
        right
        linarith
      · tauto
    constructor
    · exact proofa
    · intro f10 f2
      -- Let $S={n \in \mathbb{Z} \mid f(n) \neq 0}$. Hence we must have $S={n \in \mathbb{Z} \mid f(n)=1}$ by (a).
      set S := {x | f x ≠ 0}
      --  Since $f(1)=0,1$ is not in $S$. And $f(0)=1$ implies that $0 \in S$. Take any $x \in \mathbb{Z}$ and $y \in S$. Using (ii), we get

      -- $$ f(x y)+f(x)=f(x)+1 $$

      -- This shows that $x y \in S$. If $x \in \mathbb{Z}$ and $y \in \mathbb{Z}$ are such that $x y \in S$, 
      have hA : ∀ x y, y ∈ S → x*y ∈ S := by
        intro x y yS
        simp [S] at yS ⊢
        have y1 : f y = 1 := by have := proofa y; tauto
        specialize  h2 x y
        simp [y1] at h2
        linarith
      -- then (ii) gives
      -- $$ 1+f(x) f(y)=f(x)+f(y) $$

      -- Thus $(f(x)-1)(f(y)-1)=0$. It follows that $f(x)=1$ or $f(y)=1$; i.e., either $x \in S$ or $y \in S$.
      have hB : ∀ x y, x*y ∈ S → x ∈ S ∨ y ∈ S := by
        intro x y xyS
        specialize h2 x y
        have : f (x*y) = 1 := by simp [S] at xyS; have := proofa (x*y); tauto
        simp [this] at h2
        simp [S]
        suffices ¬ (f x = 0 ∧ f y = 0) by tauto
        intro fxfy0
        simp [fxfy0] at h2
      -- Setting $y=0$ in the condition (ii), we get
      -- We also observe from (ii) that $x \in S$ and $y \in S$ implies that $f(x-y)=1$ so that $x-y \in S$. 
      have hC : ∀ x y, x ∈ S → y ∈ S → x - y ∈ S := by
        intro x y xS yS
        simp [S] at xS yS
        specialize h3 x y
        simp [xS, yS] at h3
        have := (Int.sub_eq_zero.1 h3) ▸ h0
        simp [S, this]
      -- Now we know that $f(10) \neq 0$ and $f(2)=0$. Hence $f(10)=1$ and $10 \in S$; and $2 \notin S$. Writing $10=2 \times 5$ and using (B), we conclude that $5 \in S$ and $f(5)=1$. Hence $f(5 k)=1$ for all $k \in \mathbb{Z}$ by (A).
      have h10 : 10 ∈ S := by simp [S, f10]
      have h2  : 2 ∉ S := by simp [S, f2]
      have h5  : 5 ∈ S := by have := hB 5 2 h10; tauto
      apply Set.eq_of_subset_of_subset
      · intro a as
        have a5 := Int.ediv_add_emod' a 5
        by_cases amod5 : a % 5 = 0
        · simp; exact Int.dvd_of_emod_eq_zero amod5
        · -- Suppose $f(5 k+l)=1$ for some $l, 1 \leq l \leq 4$. Then $5 k+l \in S$.
          set k := a / 5
          set l := a % 5
          -- Choose $u \in \mathbb{Z}$ such that $l u \equiv 1(\bmod 5)$. 
          have ⟨u, hu⟩ : ∃ u, l * u ≡ 1 [ZMOD 5] := by
            use l^3
            rw [show l*l^3 = l^4 by nlinarith]
            apply Int.ModEq.pow_card_sub_one_eq_one Nat.prime_five
            have : l < 5 := by simp [l]; exact Int.emod_lt a (by omega)
            have : 0 < l := by
              have : 0 ≤ l := Int.emod_nonneg a (show 5 ≠ 0 by omega)
              omega
            interval_cases l <;> simp [Int.isCoprime_iff_gcd_eq_one] <;> decide
          -- We have $(5 k+l) u \in S$ by (A). 
          have umulS : u * (k * 5 + l) ∈ S := hA u _ (a5 ▸ as)
          have uk5S  : u * k * 5 ∈ S       := hA (u * k) _ h5
          -- --  Moreover, $l u=1+5 m$ for some $m \in \mathbb{Z}$ and
          -- $$ (5 k+l) u=5 k u+l u=5 k u+5 m+1=5(k u+m)+1 $$
          -- This shows that $5(k u+m)+1 \in S$. However, we know that $5(k u+m) \in S$. By (C), $1 \in S$ which is a contradiction.
          have oneS  : 1 ∈ S               := by
            have : l * u ∈ S := by convert hC _  _ umulS uk5S using 1; linarith
            have ⟨m, hm⟩ := Int.modEq_iff_add_fac.1 hu.symm
            convert hC _ _ this (show 5 * m ∈ S by convert hA m 5 h5 using 1; ring)
            simp [hm]
          simp [S] at oneS
          exfalso
          exact oneS h1
      · intro k ⟨y, hy ⟩
        simp [hy]
        convert hA y 5 h5  using 1
        ring