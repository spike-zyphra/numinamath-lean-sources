import Mathlib

/-- For the two-variable operation $\circ$ defined over the integers,
    it holds that for any integers $a$, $b$, and $c$,
    $$ a \circ (b+c) = b \circ a + c \circ a $$
    Show that there exists an integer $k$ such that $a \circ b = k \cdot a \cdot b$ for all $a$, $b$. -/
theorem algebra_218625 {f : ℤ → ℤ → ℤ} (h : ∀ a b c, f a (b + c) = f b a + f c a) :
    ∃ k, ∀ a b, f a b = k * a * b := by
  -- Since 0 o 0 = 0 o (0 + 0) = 0 o 0 + 0 o 0, subtracting 0 o 0 from both sides,
  -- it immediately follows that 0 o 0 = 0.
  have f_zero_zero : f 0 0 = 0 := by
    specialize h 0 0 0; simpa using h
  -- The next step is to calculate the value of 0 o a:
  have f_zero_a (a) : f 0 a = 0 := by
    -- 0 o (a+0) = ao0 + 0o0
    have eq1 : f 0 (a+0) = f a 0 + f 0 0 := h 0 a 0
    -- which equals 0oa on the LHS
    rw[add_zero] at eq1
    -- and ao0 = ao(0+0) = 0oa + 0oa.
    have eq2 : f a 0 = f 0 a + f 0 a := h a 0 0
    -- thus 0oa = 0oa + 0oa, so 0oa = 0.
    rw[f_zero_zero, eq2] at eq1
    simpa using eq1
  -- From this, the commutativiry of the o operation also follows:
  have f_comm (a b) : f a b = f b a := by
    -- a o b = a o (b + 0)
    specialize h a b 0
    -- = b o a + 0 o a = b o a.
    rwa[add_zero, f_zero_a, add_zero] at h
  -- Let x = 1 o 1. We will prove that for integers a,b, aob = a * b * x.
  let x := f 1 1
  -- We have (-1)o1 = -x:
  have f_neg_one : f (-1) 1 = -x := by
    -- Starting from 1o1 = x, we have 1o(1-1) = 1o1 + (-1) o 1 = x + (-1) o 1
    specialize h 1 1 (-1)
    simp only [Int.reduceNeg, add_neg_cancel] at h
    -- but 1-1=0, so x+(-1)o1 = 1o0 = 0, such that (-1)o1 = -x.
    rw[f_comm 1 0, f_zero_a] at h
    linarith
  have f_neg_one_neg_one : f (-1) (-1) = x := by
    specialize h (-1) 1 (-1)
    simp only [Int.reduceNeg, add_neg_cancel] at h
    rw[f_comm (-1) 0, f_comm 1 (-1), f_neg_one, f_zero_a] at h
    linarith
  -- Next, we will prove 1 o b = b * x.
  have f_one (b) : f 1 b = b * x := by
    -- We will use mathematical induction on b.
    induction b using Int.inductionOn' (b := 1) with
    -- For b = 1, the statement is true.
    | H0 => simp
    -- Suppose it is true for b = k, and let's prove it for b = k + 1.
    -- For k + 1, the statement is
    -- 1 o (k+1) = ko1 + 1o1 = 1ok + 1o1 = kx + x = (k+1) x.
    | Hs k le eq => rw[h, f_comm k 1, eq]; unfold x; ring
    -- Now we will prove the same for non-positive integers. We start from b = 1 here
    -- as well, and assume the statement holds for b = k. Then for k - 1:
    -- 1 o (k-1) = ko1 + (-1) o 1 = 1 ok + (-1) o 1 = kx + (-1) o 1,
    -- so we need to prove that (-1) o 1 = -x, as done above.
    | Hp k le eq => rw[sub_eq_add_neg, h, f_neg_one, f_comm k 1, eq]; ring
  have f_neg (b) : f (-1) b = -b * x := by
    -- Starting from 1ob=bx,
    specialize f_one b
    -- (1-1) o b = b o (1-1) = 1ob + (-1)ob = bx + (-1)ob
    have := h b 1 (-1)
    rw[f_comm b, f_one] at this
    -- but since 1-1=0, bx + (-1)ob = bo0 = 0, thus (-1)ob = -bx.
    simp only [Int.reduceNeg, add_neg_cancel, f_zero_a] at this
    linarith
  exists x
  intro a
  -- Finally, we will use mathematical induction tto prove the original statement.
  induction a using Int.inductionOn' (b := 1) with
  -- For a = 1 the statement is true because 1ob = 1 * b * x.
  | H0 => intro b; rw[f_one b]; ring
  -- Suppose it is true for a = k, then for a = k + 1:
  -- (k+1)ob = bo(k+1) = kob+1ob  = kbx + bx = (k+1)bx.
  -- Thus aob=abx for a > 0.
  | Hs k le eq => intro b; rw[f_comm (k+1) b, h, eq, f_one]; unfold x; ring
  -- Assuming it is true for a = k, for a = k-1:
  -- (k-1)ob = bo(k-1) = kob + (-1)ob = kbx + (-1)ob, so it suffices to show
  -- that (-1)ob=-bx, as done above.
  | Hp k le eq => intro b; rw[f_comm (k-1) b, sub_eq_add_neg, h, eq, f_neg]; unfold x; ring