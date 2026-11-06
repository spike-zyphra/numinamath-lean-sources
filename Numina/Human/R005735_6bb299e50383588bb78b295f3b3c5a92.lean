import Mathlib

/- The set of all ordered triples $(a, b, c)$ of positive integers such that $a b c = 2310$. -/
def S : Set (ℕ × ℕ × ℕ) := { (a, b, c) | 0 < a ∧ 0 < b ∧ 0 < c ∧ a * b * c = 2310 }

/- Define a Finset equivalent to $S$.
   `Finset.biUnion S f` is the union of the images of the function $f$ over the elements of $S$.
   `Nat.divisorsAntidiagonal n` is the set of all ordered pairs $(x, y)$ of positive integers such that $x y = n$. -/
def T : Finset (ℕ × ℕ × ℕ) :=
    Finset.biUnion (Nat.divisorsAntidiagonal 2310) (fun (x, y) => Finset.map { toFun := Prod.mk x, inj' := Prod.mk.inj_left x } (Nat.divisorsAntidiagonal y))

/- We prove that $S = T$. -/
lemma lemma_1 : S = T := by
  ext ⟨a, b, c⟩
  -- After expanding the definitions, the proposition is logically trivial.
  simp [S, T]
  constructor
  . rintro ⟨ha, hb, hc, h⟩
    use a, b * c
    simp [ne_of_gt hb, ne_of_gt hc]
    linear_combination h
  . rintro ⟨a, -, ⟨rfl, -⟩, h₁, rfl⟩
    refine ⟨?_, ?_, ?_, by linear_combination h₁⟩
    all_goals
      by_contra! h
      simp at h
      simp [h] at h₁

/- Kelvin the Frog was bored in math class one day, so he wrote all ordered triples $(a, b, c)$ of positive integers such that $a b c=2310$ on a sheet of paper. Find the sum of all the integers he wrote down. In other words, compute

$$
\sum_{\substack{a b c=2310 \\ a, b, c \in \mathbb{N}}}(a+b+c)
$$

where $\mathbb{N}$ denotes the positive integers. -/
theorem number_theory_609642 :
    ∑ᶠ p ∈ S, (let ⟨a, b, c⟩ := p; a + b + c) = 49140 := by
  -- We use the lemma to reduce the problem to a decidable proposition.
  simp [lemma_1, finsum_mem_finset_eq_sum]
  native_decide
