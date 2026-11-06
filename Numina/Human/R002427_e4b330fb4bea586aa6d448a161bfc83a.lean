import Mathlib

open Finset

/-- Find the number of triples of nonnegative integers $(a,b,c)$ satisfying $a + b + c = 300$ and
\[a^2b + a^2c + b^2a + b^2c + c^2a + c^2b = 6,000,000.\] -/
theorem algebra_93207 :
    {(a, b, c) : ℤ × ℤ × ℤ | 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 300 ∧
    a^2 * b + a^2 * c + b^2 * a + b^2 * c + c^2 * a + c^2 * b = 6000000}.ncard = 601 := by

  -- Let $p$ be the set of all triples $(a,b,c)$ satisfying the given conditions.
  set p := {(a, b, c) : ℤ × ℤ × ℤ | 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 300 ∧
    a^2 * b + a^2 * c + b^2 * a + b^2 * c + c^2 * a + c^2 * b = 6000000}

  -- Observe that, provided $a + b + c = 300$, the other equation can be rewritten as
  -- $-3 (a - 100) (b - 100) (c - 100) + 6000000$. This follows from simple algebraic manipulation
  -- and greedily substituting $a + b + c = 300$.
  have lem {a b c : ℤ} (h : a + b + c = 300) :
      a^2 * b + a^2 * c + b^2 * a + b^2 * c + c^2 * a + c^2 * b =
      -3 * (a - 100) * (b - 100) * (c - 100) + 6000000 := by
    calc _ = a * b * (a + b) + b * c * (b + c) + a * c * (a + c) := by ring
         _ = a * b * (300 - c) + b * c * (300 - a) + a * c * (300 - b) := by rw [←h]; ring
         _ = 300 * (a * b + a * c + b * c) - 3 * a * b * c := by ring
         _ = -3 * ((a - 100) * (b - 100) * (c - 100) - 10000 * (a + b + c) + 1000000) := by ring
         _ = _ := by rw [h]; ring

  -- Let $q$ be the set of all triples $(a,b,c)$ of nonnegative integers such that $a + b + c = 300$
  -- and one of $a$, $b$, or $c$ is equal to $100$.
  set q := {(a, b, c) : ℤ × ℤ × ℤ | 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 300 ∧
    (a = 100 ∨ b = 100 ∨ c = 100)}

  -- It suffices to show that $q$ has $601$ elements because the observation above clearly shows
  -- that $p = q$.
  suffices q.ncard = 601 from ?_
  · rw [←this]
    congr
    ext ⟨a, b, c⟩
    constructor
    · rintro ⟨anneg, bnneg, cnneg, h1, h2⟩
      refine ⟨anneg, bnneg, cnneg, h1, ?_⟩
      simp [lem h1] at h2
      omega
    · rintro ⟨anneg, bnneg, cnneg, h1, h2⟩
      refine ⟨anneg, bnneg, cnneg, h1, ?_⟩
      simp [lem h1]
      omega

  -- Now, let's show that $q$ has $601$ elements.
  -- To that end,
  -- let $r$ be the set of all triples $(100, b, 200-b)$ where $b$ is a nonnegative integer less
  -- than or equal to $200$.
  -- Let $s$ be the set of all triples $(200-c,100,c)$ where $c$ is a nonnegative integer less than
  -- or equal to $200$.
  -- Let $t$ be the set of all triples $(a,200-a,100)$ where $a$ is a nonnegative integer less than
  -- or equal to $200$.
  let r : Finset (ℤ × ℤ × ℤ) := (image (fun b ↦ (100, b, 200 - b)) (Icc (0:ℤ) 200))
  let s : Finset (ℤ × ℤ × ℤ) := (image (fun c ↦ (200 - c, 100, c)) (Icc (0:ℤ) 200))
  let t : Finset (ℤ × ℤ × ℤ) := (image (fun a ↦ (a, 200 - a, 100)) (Icc (0:ℤ) 200))

  -- It suffices to show that $r \cup s \cup t$ has $601$ elements because $q = r \cup s \cup t$.
  suffices (r ∪ s ∪ t).card = 601 from ?_
  · rw [←this, ←Set.ncard_coe_Finset, coe_union, coe_union, coe_image,
        coe_image, coe_image, coe_Icc]
    apply congr_arg
    ext ⟨a, b, c⟩
    constructor
    · rintro ⟨anneg, bnneg, cnneg, h1, h2 | h2 | h2⟩
      · left; left
        exact ⟨b, ⟨bnneg, by omega⟩, by simp; omega⟩
      · left; right
        exact ⟨c, ⟨cnneg, by omega⟩, by simp; omega⟩
      · right
        exact ⟨a, ⟨anneg, by omega⟩, by simp; omega⟩
    · rintro ((⟨_, ⟨bnneg, b_le⟩, ⟨rfl, rfl, rfl⟩⟩ | ⟨_, ⟨cnneg, c_le⟩, ⟨rfl, rfl, rfl⟩⟩) |
          ⟨_, ⟨anneg, a_le⟩, ⟨rfl, rfl, rfl⟩⟩)
      · exact ⟨by norm_num, bnneg, by omega, by ring, by left; rfl⟩
      · exact ⟨by omega, by norm_num, cnneg, by ring, by right; left; rfl⟩
      · exact ⟨anneg, by omega, by norm_num, by ring, by right; right; rfl⟩

  -- Now, let's show that $r \cup s \cup t$ has $601$ elements. First, we use the inclusion-exclusion
  -- principle to rewrite the cardinality of the union of $r$, $s$, and $t$ in terms of the cardinalities
  -- of the intersections of $r$, $s$, and $t$.
  rw [card_union, card_union, union_inter_distrib_right, card_union,
      inter_assoc, inter_comm s t, ←inter_assoc t t s, inter_self,
      ←inter_assoc r t s]

  rw [card_image_of_injective, card_image_of_injective, card_image_of_injective]
  rotate_left
  · intro _ _; simp
  · intro _ _; simp
  · intro _ _; simp

  -- The cardinalities of $r$, $s$, and $t$ are $201$, $201$, and $201$, respectively.
  simp [Int.card_Icc]

  -- Substituting these values into the equation, we see that it is enough to show that the
  -- intersections are all singletons. Actually, they are all equal to the singleton $\{(100,100,100)\}$.
  suffices (r ∩ t = {(100, 100, 100)}) ∧ (r ∩ s = {(100, 100, 100)}) ∧
      (t ∩ s = {(100, 100, 100)}) ∧ (r ∩ (t ∩ s) = {(100, 100, 100)}) from ?_
  · rw [this.2.2.2, this.2.2.1, this.2.1, this.1, card_singleton]

  -- This is because if two of $a, b, c$ are 100, then the equation $a + b + c = 300$ forces the
  -- third to be 100 as well. 
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext ⟨a, b, c⟩ <;> simp [r, s, t]
  · constructor
    · rintro ⟨⟨_, _, rfl, rfl, rfl⟩, ⟨_, _, rfl, rfl, _⟩⟩; simp
    · rintro ⟨rfl, rfl, rfl⟩; simp
      exact ⟨100, by norm_num⟩
  · constructor
    · rintro ⟨⟨_, _, rfl, rfl, rfl⟩, ⟨_, _, _, rfl, _⟩⟩; simp
    · rintro ⟨rfl, rfl, rfl⟩; simp
      exact ⟨100, by norm_num⟩
  · constructor
    · rintro ⟨⟨_, _, rfl, rfl, rfl⟩, ⟨_, _, rfl, _, rfl⟩⟩; simp
    · rintro ⟨rfl, rfl, rfl⟩; simp
      exact ⟨100, by norm_num⟩
  · constructor
    · rintro ⟨⟨_, _, rfl, rfl, rfl⟩, ⟨_, _, rfl, rfl, _⟩, _⟩; simp
    · rintro ⟨rfl, rfl, rfl⟩; simp
      exact ⟨100, by norm_num⟩