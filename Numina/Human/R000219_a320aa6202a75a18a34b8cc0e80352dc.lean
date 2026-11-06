import Mathlib

/- Let  $\mathbb{N} = \{1, 2, 3, \ldots\}$  be the set of positive integers. Find all functions  $f$ , defined on  $\mathbb{N}$  and taking values in  $\mathbb{N}$ , such that  $(n-1)^2< f(n)f(f(n)) < n^2+n$  for every positive integer  $n$ .-/
theorem number_theory_8604 {f : ℕ → ℕ} (hfpos : ∀ n > 0, f n > 0)
    (hf : ∀ n > 0, (n - 1)^2 < f n * f (f n) ∧ f n * f (f n) < n^2 + n) :
    ∀ n > 0, f n = n := by
  intro n hn
  -- We claim that  $f(n)=n$  is the only such function that works.
  -- Use strong induction.
  induction' n using Nat.strongRecOn with n ih
  --  Now assume that  $f(i)=i$  for each  $1\leq i\leq k-1$ .
  --  In order to evaluate  $f(k)$ ,
  --  we bound, and to do this we split up the proof into two distinct cases.
  rcases lt_trichotomy (f n) n with hfnlt | hfneq | hfngt
  -- - **CASE 1:** Suppose  $f(k) < k$ .
  -- Let  $f(k)=k_0$ ; then by the induction hypothesis  $f(k_0)=k_0$ .
  -- But since  $k_0$  is a positive integer we must have  $k_0\leq k-1$ ,
  -- so \[f(k)f(f(k))=k_0f(k_0)=k_0^2 < (k-1)^2,\] which contradicts the problem statement.
  -- Hence  $f(k)\geq k$ .
  . exfalso
    set m := f n with hm
    have hmpos : 0 < m := hfpos _ hn
    have hmle : m ≤ n - 1 := by omega
    have hmsqle : m * m ≤ (n - 1) * (n - 1) := by nlinarith
    have hfm : f m = m := ih m hfnlt hmpos
    have := hf n hn
    rw [← hm, hfm] at this
    linarith
  -- f n = n is what we need.
  . exact hfneq
  -- - **CASE 2:** Suppose  $f(k)>k$ .
  -- Once again, let  $f(k)=k_0$ .
  -- Unfortunately, we are not able to derive  $f(k_0)=k_0$  from this
  -- because the inductive hypothesis does not stretch up to  $f(k_0)$ .
  -- To tackle this, we once again split into cases.
  . set m := f n
    have hmpos : 0 < m := hfpos _ hn
    rcases le_or_lt n (f m) with hfmge | hfmlt
    -- - If  $f(k_0)\geq k$ , then a simple bounding argument reveals that
    -- \[f(k)f(f(k))=k_0f(k_0)\geq k_0k\geq (k+1)k=k^2+k,\] contradiction.
    . specialize hf n hn
      have : n ^ 2 + n ≤ (f n) * (f (f n)) := by nlinarith
      linarith
    -- - If  $f(k_0)< k$ , then let  $f(k_0)=k_1$ .
    -- We cannot necessarily deduce anything from
    -- plugging in  $n=k$  into the problem statement functional equation,
    -- but now consider what happens when  $n=k_1$ .
    -- In this case, an argument analogous to **CASE 1** occurs:
    -- we have \[f(k_0)f(f(k_0))=k_1f(k_1)=k_1^2<(k_0-1)^2,\] contradiction.
    set m1 := f m with hm1
    have hm1pos : 0 < m1 := hfpos _ hmpos
    have hm1lt : m1 < m := by linarith
    have hm1le : m1 ≤ m - 1 := by omega
    have hm1sqle : m1 * m1 ≤ (m - 1) * (m - 1) := by nlinarith
    have hfm1 : f m1 = m1 := ih m1 hfmlt hm1pos
    have := hf m hmpos
    rw [show  (f m) * (f (f m)) = m1 * m1 by rw [← hm1, hfm1]] at this
    linarith
