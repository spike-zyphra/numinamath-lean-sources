import Mathlib

/-Let $S(k)$ denote the sum of the digits of a positive integer $k$. Let $f(k) = (S(k))^2$.
Let $f^1(k) = f(k)$ and for $n \ge 2$, let $f^n(k) = f(f^{n-1}(k))$.Let $N$ be a positive integer. Show that $f^N(11)$ takes one of the following values:if $N=1$, $f^N(11) = 4$;if $N=2$, $f^N(11) = 16$;if $N=3$, $f^N(11) = 49$;if $N \ge 4$ and $N$ is even, $f^N(11) = 169$;if $N \ge 4$ and $N$ is odd, $f^N(11) = 256$.-/
theorem eleven_compute
  (hk:k=10)
  (hf:f=fun x=>((k.digits x).sum)^2):
  ∀ n, (n=1→ f^[n] 11=4)∧
  (n=2→ f^[n] 11=16)∧
  (n=3→ f^[n] 11=49)∧
  (n≥ 4→ ((Even n→ f^[n] 11=169)∧
  (Odd n→ f^[n] 11=256))):=
by
  -- Introduce the universal quantifier variable
  intro n
  -- Split the conjunction into separate goals
  split_ands
  -- Handle the case when n=1
  intro h0
  rw[h0]
  simp
  rw[hf,hk]
  simp

  -- Handle the case when n=2
  intro h0
  rw[h0]
  rw[hf,hk]
  simp

  -- Handle the case when n=3
  intro h0
  rw[h0]
  rw[hf,hk]
  simp

  -- Handle the case when n ≥ 4
  intro h0
  -- Use induction on n
  induction n with
  | zero =>
    -- Derive a contradiction since n cannot be 0 when n ≥ 4
    contrapose! h0
    norm_num
  | succ n0 ih =>
    -- Split into cases: n0 < 4 or n0 ≥ 4
    have hcase:n0<4∨ n0≥ 4:=by
      exact Nat.lt_or_ge n0 4
    rcases hcase with hl|hr
    -- Handle the case when n0 = 3
    have heq:n0=3:=by
      refine Nat.le_antisymm ?_ ?_
      exact Nat.le_of_lt_succ hl
      exact Nat.le_of_lt_succ h0
    split_ands
    intro h
    rw[heq,hf,hk]
    simp
    intro h
    contrapose! h
    rw[heq]
    norm_num
    use 2

    -- Apply induction hypothesis for the case n0 ≥ 4 and n is odd
    apply ih at hr
    intro h
    have hodd:Odd n0:=by
      contrapose! h
      simp
      exact Nat.odd_add_one.mpr h
    apply hr.2 at hodd
    rw[Function.iterate_succ']
    have hsimp:(f ∘ f^[n0]) 11 =f (f^[n0] 11 ):=by exact rfl
    rw[hsimp,hodd,hf,hk]
    simp

    -- Apply induction hypothesis for the case n0 ≥ 4 and n is even
    intro h
    have heven:Even n0:=by
      contrapose! h
      simp
      exact Nat.even_add_one.mpr h
    apply ih at hr
    apply hr.1 at heven
    rw[Function.iterate_succ']
    have hsimp:(f ∘ f^[n0]) 11 =f (f^[n0] 11 ):=by exact rfl
    rw[hsimp,heven,hf,hk]
    simp