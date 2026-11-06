import Mathlib
/--
Find all functions $f: \mathbb{R} \rightarrow \mathbb{R}$ such that for all $x, y \in \mathbb{R}$,

$$
x f(x+f(y))=(y-x) f(f(x)).
$$

Answer: Either, for some $c$, $f(x)=c-x$ for all $x$ or $f(x)=0$ for all $x$.
-/
theorem algebra_604945 (f : ℝ → ℝ) : (∀ x y : ℝ, x * f (x + f y) = (y - x) * f (f x))
    ↔ (∃ c : ℝ, ∀ x, f x = c - x) ∨ (∀ x, f x = 0) := by
  constructor
  · intro hf

    -- Let $P(x, y)$ denote the proposition that $x$ and $y$ satisfy the given equation.
    -- $P(0,1)$ gives us $f(f(0))=0$.
    have hf0 : f (f 0) = 0 := by
      have := hf 0 1
      rw [zero_add, zero_mul, sub_zero, one_mul] at this
      exact Eq.symm this

    -- From $P(x, x)$ we get that $x f(x+f(x))=0$ for all $x \in \mathbb{R}$, which together with $f(f(0))=0$ gives us $f(x+f(x))=0$ for all $x$.
    have hfx (x : ℝ) : f (x + f x) = 0 := by
      have := hf x x
      rw [sub_self, zero_mul, mul_eq_zero] at this
      obtain h | h := this
      · simp only [h, zero_add]
        exact hf0
      · exact h

    -- Now let $t$ be any real number such that $f(t)=0$. If $y$ is any number, we have from $P(t-f(y), y)$ the equality
    -- $ (y+f(y)-t) f(f(t-f(y)))=0 $
    -- for all $y$ and all $t$ such that $f(t)=0$. So, by taking $y=f(0)$ we obtain
    -- $$ (f(0)-t) f(f(t))=0 \quad \text{and hence} \quad (f(0)-t) f(0)=0 $$
    have hft (t : ℝ) : f t = 0 → (f 0 - t) * f 0 = 0 := by
      intro ht
      have := hf (t - f (f 0)) (f 0)
      rw [hf0, sub_zero, add_zero, ht, mul_zero] at this
      exact Eq.symm this

    -- If for all reals $x$ we have $x+f(x)=f(0)$, then $f(x)$ must be of the form $f(x)=c-x$ for some real $c$.
    by_cases hc : (∀ x, x + f x = f 0)
    · left; use f 0
      exact fun x => eq_sub_of_add_eq' (hc x)

    -- Otherwise we can find some $a \neq 0$ so that $a+f(a) \neq f(0)$. If $t=a+f(a)$ in (A1-1), then $f(0)$ must be equal to 0.
    · have hf0' : f 0 = 0 := by
        rw [not_forall] at hc
        obtain ⟨a, ha⟩ := hc
        have := hft (a + f a) (hfx a)
        rw [mul_eq_zero] at this
        obtain h | h := this
        · rw [sub_eq_iff_eq_add, zero_add] at h
          rw [h] at ha
          exfalso
          exact ha rfl
        · exact h

      -- Now $P(x, 0)$ gives us $f(f(x))=-f(x)$ for all real $x$.
      have hff (x : ℝ) : f (f x) = - f x := by
        have := hf x 0
        rw [hf0', add_zero, zero_sub, neg_mul, ← add_eq_zero_iff_eq_neg, ← mul_add,
          mul_eq_zero] at this
        obtain h | h := this
        · rw [h, hf0, hf0']
          exact zero_eq_neg.mpr rfl
        · exact Eq.symm (neg_eq_of_add_eq_zero_right h)

      -- which means for every $x$ either $f(x)=0$ or $f(x)=-x$.
      have hor (x : ℝ) :  f x = 0 ∨ f x + x = 0 := by
        rw [or_comm, ← mul_eq_zero, add_comm]
        have := hf x (x + f x)
        rw [add_sub_cancel_left, hff x, hfx x, add_zero, mul_neg, ← add_eq_zero_iff_eq_neg,
          ← add_mul] at this
        exact this

      -- Let us assume that there is some $b \neq 0$ so that $f(b)=-b$.
      by_cases hc : ∃ b ≠ 0, f b = - b

      -- For any $y$ we get from $P(b, y)$ and $f(f(b))=-f(b)=b$ the equality $b f(b+f(y))=(y-b) b$, which gives us $f(b+f(y))=y-b$ for all $y$.
      · obtain ⟨b, ⟨hbne0, hb⟩⟩ := hc
        have hfb (y : ℝ) : f (b + f y) = y - b := by
          have := hf b y
          rw [hff b, hb, neg_neg, mul_comm, mul_eq_mul_right_iff] at this
          obtain h | h := this
          · exact h
          · exact False.elim (hbne0 h)

        -- If $y \neq b$, then the right hand side in the previous equality is not zero, so we must have $f(b+f(y))=-b-f(y)$, which means that $-b-f(y)=y-b$, or that $f(y)=-y$ for all real $y$. But we already covered this solution (take $c=0$ above).
        left; use 0
        simp only [zero_sub]
        intro y
        obtain h | h := hor (b + f y)
        · rw [hfb y, sub_eq_iff_eq_add, zero_add] at h
          rw [h]
          exact hb
        · rw [hfb, ← add_assoc, add_comm, sub_add_cancel] at h
          exact eq_neg_of_add_eq_zero_left h

      -- If there is no such $b$, then $f(x)=0$ for all $x$, which gives us the final solution.
      · push_neg at hc
        right
        intro x
        obtain h | h := hor x
        · exact h
        · by_cases hc' : x ≠ 0
          · rw [add_comm, add_eq_zero_iff_neg_eq] at h
            have := hc x hc'
            rw [h] at this
            contradiction
          · push_neg at hc'
            rw [hc', hf0']

  -- It is easy to show that both solutions satisfy the given equation
  · intro hf
    obtain ⟨c, hc⟩ | h := hf
    · intro x y
      simp [hc]
      ring
    · simp [h]
      