import Mathlib

/-- 30. Find the number of ordered triples of integers $(a, b, c)$
        with $1 \leq a, b, c \leq 100$ and $a^{2} b+b^{2} c+c^{2} a=$ $a b^{2}+b c^{2}+c a^{2}$. -/
theorem algebra_163112 :
    Set.ncard {(a, b, c) : ℕ × ℕ × ℕ | 1 ≤ a ∧ a ≤ 100 ∧ 1 ≤ b ∧ b ≤ 100 ∧ 1 ≤ c ∧ c ≤ 100 ∧
      a^2 * b + b^2 * c + c^2 * a = a * b^2 + b * c^2 + c * a^2} = 29800 := by
  -- Subtract the both terms, then the statement simplified to (a-b)(b-c)(c-a) = 0
  have (a b c : ℕ) : a^2 * b + b^2 * c + c^2 * a = a * b^2 + b * c^2 + c * a^2 ↔ (a = b ∨ b = c ∨ c = a) := by
    zify
    trans ((a :ℤ) - b) * (b - c) * (c-a) = 0
    · rw[← sub_eq_zero, ← neg_eq_zero]
      apply Eq.congr_left
      ring
    -- hence a = b, b = c or a = c.
    · simp only [mul_eq_zero, sub_eq_zero, Nat.cast_inj]
      apply or_assoc
  simp_rw[this]
  -- So the set of considered integers is given by {(a,b,c)| 1 <= a,b,c <= 100, a = b or a = c or b = c}.
  let A := {x : ℕ × ℕ × ℕ |
      1 ≤ x.1 ∧
        x.1 ≤ 100 ∧
          1 ≤ x.2.1 ∧ x.2.1 ≤ 100 ∧ 1 ≤ x.2.2 ∧ x.2.2 ≤ 100 ∧ (x.1 = x.2.1 ∨ x.2.1 = x.2.2 ∨ x.2.2 = x.1)}
  let f1 (x : ℕ × ℕ) := (x.1,x.1,x.2)
  let f2 (x : ℕ × ℕ) := (x.2,x.1,x.1)
  let f3 (x : ℕ × ℕ) := (x.1,x.2,x.1)
  let f' (x : ℕ) := (x,x,x)
  -- This is equal to f1 '' [1,100]^2 ∪ f2 '' [1,100]^2 ∪ f3 '' [1,100]^2
  -- where f1(a,b) = (a,a,b), f2(a,b) = (b,a,a), f3(a,b) = (a,b,a).
  have eqA : A = f1 '' (Finset.Icc 1 100 ×ˢ Finset.Icc 1 100) ∪
      f2 '' (Finset.Icc 1 100 ×ˢ Finset.Icc 1 100) ∪ f3 '' (Finset.Icc 1 100 ×ˢ Finset.Icc 1 100) := by
    ext ⟨a,b,c⟩
    unfold A
    constructor
    · rintro ⟨ge1,le1,ge2,le2,ge3,le3,(eq|eq|eq)⟩
      · left; left; exists (a,c); simp[f1, *]; exact ⟨⟨ge1,ge3⟩, eq⟩
      · left; right; exists (b,a); simp[f2, *]; exact ⟨⟨ge2,ge1⟩, eq⟩
      · right; exists (c,b); simp[f3, *]; exact ⟨⟨ge3,ge2⟩, eq⟩
    · rintro ((⟨⟨d,e⟩,mem,⟨rfl,rfl,rfl⟩⟩|
                ⟨⟨d,e⟩,mem,⟨rfl,rfl,rfl⟩⟩)|
                ⟨⟨d,e⟩,mem,⟨rfl,rfl,rfl⟩⟩)
      · simp at *
        obtain ⟨⟨led,ged⟩,⟨lee,gee⟩⟩ := mem
        split_ands <;> assumption
      · simp at *
        obtain ⟨⟨led,ged⟩,⟨lee,gee⟩⟩ := mem
        split_ands <;> assumption
      · simp at *
        obtain ⟨⟨led,ged⟩,⟨lee,gee⟩⟩ := mem
        split_ands <;> assumption
  unfold A at eqA
  rw[eqA]
  have ff1 : Set.Finite $ f1 '' ↑(Finset.Icc 1 100) ×ˢ ↑(Finset.Icc 1 100) :=
    Set.Finite.image _ $ Set.Finite.prod (Finset.finite_toSet _) (Finset.finite_toSet _)
  have ff2 : Set.Finite $ f2 '' ↑(Finset.Icc 1 100) ×ˢ ↑(Finset.Icc 1 100) :=
    Set.Finite.image _ $ Set.Finite.prod (Finset.finite_toSet _) (Finset.finite_toSet _)
  have ff3 : Set.Finite $ f3 '' ↑(Finset.Icc 1 100) ×ˢ ↑(Finset.Icc 1 100) :=
    Set.Finite.image _ $ Set.Finite.prod (Finset.finite_toSet _) (Finset.finite_toSet _)
  have if1 : Function.Injective f1 := by intro (a,b) (d,e) eq; simp[f1] at eq; simp[*]
  have if2 : Function.Injective f2 := by intro (a,b) (d,e) eq; simp[f2] at eq; simp[*]
  have if3 : Function.Injective f3 := by intro (a,b) (d,e) eq; simp[f3] at eq; simp[*]
  have if' : Function.Injective f' := by intro a d eq; simp[f'] at eq; simp[*]
  have := Set.Finite.union ff1 ff2
  -- By inclusion/exclusion, the cardinality of that set equals
  -- |f1 '' [1,100]^2| + |f2 '' [1,100]^2 ∪ f3 '' [1,100]^2| - |f1 '' [1,100]^2 ∩ (f2 '' [1,100]^2 ∪ f3 '' [1,100]^2)|.
  have card_union := Set.ncard_inter_add_ncard_union (hs := this) (ht := ff3)
  -- The first term simplifies to |[1,100]|^2 due to injectivity of f1.
  rw[Set.ncard_image_of_injective _ if3] at card_union
  -- We show that the intersection equals {(a,a,a)|1<=a<=100},
  have inter_eq : ((f1 '' ↑(Finset.Icc 1 100) ×ˢ ↑(Finset.Icc 1 100) ∪ f2 '' ↑(Finset.Icc 1 100) ×ˢ ↑(Finset.Icc 1 100)) ∩
           f3 '' ↑(Finset.Icc 1 100) ×ˢ ↑(Finset.Icc 1 100)) = f' '' (Finset.Icc 1 100) := by
    ext ⟨d,e,f⟩
    constructor
    · rintro ⟨(⟨⟨a,b⟩,⟨ha,hb⟩,eq⟩|⟨⟨a,b⟩,⟨ha,hb⟩,eq⟩),⟨⟨a',b'⟩,⟨ha',hb'⟩,eq'⟩⟩
      · simp[f1,f3] at eq eq' ha
        simp[f']
        exists d
        rw[← eq.2.1, eq.1, ← eq'.2.2, eq'.1]
        simp only [and_self, and_true]
        rwa[eq.1] at ha
      · simp[f2,f3] at eq eq' ha
        simp[f']
        exists a
        have : a = d := eq.2.2.trans $ eq'.2.2.symm.trans eq'.1
        rw[← this, ← eq.2.1, ← eq.2.2]
        simp[ha]
    · rintro ⟨a,mem,eq⟩
      simp[f'] at eq
      obtain ⟨rfl,rfl,rfl⟩ := eq
      simp only [Finset.coe_Icc, Set.Icc_prod_Icc, Prod.mk_one_one, Set.mem_inter_iff,
        Set.mem_union, Set.mem_image, Set.mem_Icc, Prod.exists, Prod.mk_le_mk]
      simp at mem
      have ⟨le,ge⟩ := mem
      constructor
      · left; use a; use a; simp[*]; exact ⟨le,le⟩
      · use a; use a; simp[*]; exact ⟨le,le⟩
  -- hence we arrive at 9900 + |f2 '' [1,100]^2 ∪ f3 '' [1,100]^2|.
  rw[inter_eq] at card_union
  rw[Set.ncard_image_of_injective _ if'] at card_union
  simp at this
  have card_union' := Set.ncard_inter_add_ncard_union (hs := ff1) (ht := ff2)
  -- Repeat this procedure - by injectivity, this set has 20000 - 100 = 19900 elements.
  have inter : (f1 '' ↑(Finset.Icc 1 100) ×ˢ ↑(Finset.Icc 1 100) ∩ f2 '' ↑(Finset.Icc 1 100) ×ˢ ↑(Finset.Icc 1 100)) = f' '' (Finset.Icc 1 100) := by
    ext ⟨d,e,f⟩
    constructor
    · rintro ⟨⟨⟨a,b⟩,⟨ha,hb⟩,eq⟩,⟨⟨a',b'⟩,⟨ha',hb'⟩,eq'⟩⟩
      simp[f1,f2] at eq eq' ha
      simp[f']
      have : a = f := eq.2.1.trans $ eq'.2.1.symm.trans eq'.2.2
      exists a
      exact ⟨ha,eq.1,eq.2.1,this⟩
    · rintro ⟨a,mem,eq⟩
      simp[f'] at eq
      obtain ⟨rfl,rfl,rfl⟩ := eq
      simp only [Finset.coe_Icc, Set.Icc_prod_Icc, Prod.mk_one_one, Set.mem_inter_iff,
        Set.mem_union, Set.mem_image, Set.mem_Icc, Prod.exists, Prod.mk_le_mk]
      simp at mem
      have ⟨le,ge⟩ := mem
      constructor
      · use a
        use a
        simp only [mem.2, and_self, and_true, Prod.mk.eta, f1]
        exact ⟨le,le⟩
      · use a
        use a
        simp only [mem.2, and_self, and_true, Prod.mk.eta, f1]
        exact ⟨le,le⟩
  rw[inter, Set.ncard_image_of_injective _ if1, Set.ncard_image_of_injective _ if', Set.ncard_image_of_injective _ if2] at card_union'
  have int_card : Set.ncard (↑(Finset.Icc (1 : ℕ) 100) : Set ℕ) = 100 := by
    rw[Set.ncard_coe_Finset]
    simp
  have int_card' : Set.ncard ((↑(Finset.Icc (1 : ℕ) 100) : Set ℕ) ×ˢ (↑(Finset.Icc (1 : ℕ) 100) : Set ℕ)) = 10000 := by
    rw[← Finset.coe_product, Set.ncard_coe_Finset]
    simp
  simp [- Finset.coe_Icc, - Set.Icc_prod_Icc, int_card, int_card'] at card_union' card_union
  -- By adding the two, we arrive at the desired result.
  have : (f1 '' ↑(Finset.Icc 1 100) ×ˢ ↑(Finset.Icc 1 100) ∪ f2 '' ↑(Finset.Icc 1 100) ×ˢ ↑(Finset.Icc 1 100)).ncard = 19900 := by
    linarith
  rw[this] at card_union
  linarith