import Mathlib

open Finset

/- All the students in an algebra class took a $100$-point test. Five students scored $100$, each student scored at least $60$, and the mean score was $76$. What is the smallest possible number of students in the class?
$\mathrm{(A)}\ 10 \qquad \mathrm{(B)}\ 11 \qquad \mathrm{(C)}\ 12 \qquad \mathrm{(D)}\ 13 \qquad \mathrm{(E)}\ 14$ -/
theorem algebra_1151 : IsLeast { n | ∃f: range n -> ℕ,
      -- First 5 values of `f` are `100`.
      ∃p: n ≥ 5, (∀i: ℕ, ∀q: i < 5, f ⟨i, by simp_all only [mem_range]; linarith⟩ = 100)
      ∧ (∀i : range n, f i ≥ 60 ∧ f i ≤ 100 )
      ∧ (∑ k : range n, (f k / n : ℚ) = 76)
    } 13 := by
  simp only [mem_range, ge_iff_le, Subtype.forall, exists_and_right]
  constructor

  case right =>
    rw [mem_lowerBounds]
    intro n
    rw [Set.mem_setOf_eq]
    intro ⟨f, ⟨p,p'⟩, q, r⟩

    -- At the same time, we need to achieve the mean $76$, which is equivalent to achieving the sum $76n$.
    symm at r
    rw [<- Finset.sum_div (α := ℚ) _ _ n] at r
    apply_fun (· * ↑n) at r
    rw [div_mul_cancel₀] at r
    case h => apply ne_of_gt; norm_cast; linarith
    norm_cast at r

    -- Hence we get a necessary condition on $n$: we must have $5\cdot 100 + (n-5)\cdot 60 \leq 76n$.
    -- It is more convenient to extend the range of `f` to `ℕ`.
    let f' (i: ℕ) := if p: i < n then f ⟨i, by simp; exact p⟩ else 0

    have h (i: range n) : f i = f' i := by
      unfold_let; have h := mem_range.1 i.2; simp; split <;> rfl

    have h' (i: ℕ) (p: i < n) : f ⟨i, mem_range.2 p⟩ = f' i := by
      unfold_let; simp; split <;> rfl

    simp_rw [h, Finset.sum_coe_sort] at r
    nth_rw 2 [<- Nat.sub_add_cancel p] at r
    rw [add_comm, Finset.sum_range_add] at r

    have eval_1: ∑ x ∈ range 5, f' x = ∑ x ∈ range 5, 100 := by
      apply Finset.sum_congr rfl
      intro i p
      apply mem_range.1 at p
      rw [<- h' i (by linarith), p' i p]

    have eval_2: ∑ x ∈ range (n - 5), f' (5 + x) ≥ ∑ x ∈ range (n - 5), 60 := by
      -- Rewriting inside binder..
      apply Finset.sum_le_sum
      intro i p
      apply mem_range.1 at p
      apply Nat.add_lt_of_lt_sub at p
      rw [add_comm] at p
      specialize q (5 + i) p
      rw [<- h' _ p]
      exact q.1

    have t: 76 * n ≥ 500 + (n - 5) * 60 := by
      calc
        76 * n = 500 + ∑ x ∈ range (n - 5), f' (5 + x) := by
           rw [r, eval_1]
           simp
        _ ≥ 500 + ∑ x ∈ range (n - 5), 60 := by gcongr
        _ ≥ 500 + (n - 5) * 60 := by simp


    -- This can be simplified to $200 \leq 16n$. The smallest integer $n$ for which this is true is $n=13$.
    -- `linarith` is a bit picky with its casts.
    rw [ge_iff_le, <- Int.ofNat_le] at t
    push_cast [Nat.cast_sub p, Int.Nat.cast_ofNat_Int] at t
    linarith


  /- To finish our solution, we now need to find one way how $13$ students could have scored on the test. We have $13\cdot 76 = 988$ points to divide among them. The five $100$s make $500$, hence we must divide the remaining $488$ points among the other $8$ students. This can be done e.g. by giving $61$ points to each of them. -/
  case left =>
    simp only [univ_eq_attach, Set.mem_setOf_eq, Nat.reduceLeDiff, exists_true_left, Nat.cast_ofNat]

    let f (i: range 13) := if (i : ℕ) < 5 then 100 else 61
    use f
    unfold_let
    simp
    constructor
    case left => intro i q; constructor <;> split <;> linarith
    case right => native_decide