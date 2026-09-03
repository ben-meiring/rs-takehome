import HeadComplexity.Results.LowComplexity
set_option linter.style.emptyLine false

/-!

# Complement symmetry obstruction

A nonconstant Boolean function satisfying

`f (¬x) = f x`

cannot be represented by an affine threshold function. Consequently, its
threshold degree is at least two and its attention-head complexity satisfies

`2 ≤ HStar n f`.

The proof works directly in `{0,1}` coordinates. For an affine score

`S(x) = a₀ + ∑ i, a i * boolToReal (x i)`,

the sum of the scores at complementary inputs is independent of `x`:

`S(x) + S(¬x) = 2a₀ + ∑ i, a i`.

Complement symmetry requires `x` and `¬x` to receive the same label. If the
function is nonconstant, one complementary pair must receive the positive label
and another the negative label. Their score sums would therefore have opposite
signs, contradicting the fact that both sums equal the same constant.

The file proves the obstruction first for affine separators, translates it into
`¬ isLTF f` and `¬ ThresholdDegLE f 1`, and finally applies the repository's
one-head characterization to obtain the lower bound on `HStar`.

-/


namespace HeadComplexity
open scoped BigOperators
variable {n : ℕ}

/--
A nonconstant Boolean function invariant under global bit complementation cannot
be sign-represented by an affine function.
-/
theorem no_affine_separator
    (f : (Fin n → Bool) → Bool)
    (hflip : ∀ x, f (fun i ↦ !(x i)) = f x)
    (hnonconst : ∃ x y, f x ≠ f y) :
    ¬ ∃ a₀ : ℝ, ∃ a : Fin n → ℝ,
      ∀ x,
        (0 < a₀ + ∑ i, a i * boolToReal (x i) ↔ f x = true) := by
  -- Assume that an affine separator exists.
  rintro ⟨a₀, a, hsep⟩

  -- Choose two inputs on which the nonconstant function differs.
  rcases hnonconst with ⟨x, y, hxy⟩

  -- A Boolean coordinate and its complement sum to one.
  have hbit (b : Bool) :
      boolToReal b + boolToReal (!b) = 1 := by
    cases b <;> simp [boolToReal]

  -- The sum of an affine score at u and at its complement is independent of u.
  have hpair (u : Fin n → Bool) :
      (a₀ + ∑ i, a i * boolToReal (u i)) +
          (a₀ + ∑ i, a i * boolToReal (!(u i)))
        = 2 * a₀ + ∑ i, a i := by
    calc
      _ = 2 * a₀ +
          ∑ i, a i * (boolToReal (u i) + boolToReal (!(u i))) := by
            simp_rw [mul_add]
            rw [Finset.sum_add_distrib]
            ring
      _ = 2 * a₀ + ∑ i, a i := by
            apply congrArg (fun t : ℝ ↦ 2 * a₀ + t)
            apply Finset.sum_congr rfl
            intro i _
            rw [hbit, mul_one]

  -- Name the affine score and global-complement operation.
  let S : (Fin n → Bool) → ℝ :=
    fun u ↦ a₀ + ∑ i, a i * boolToReal (u i)

  let flip : (Fin n → Bool) → (Fin n → Bool) :=
    fun u i ↦ !(u i)

  -- Complement invariance expressed using the local name `flip`.
  have hflip' (u : Fin n → Bool) :
      f (flip u) = f u := by
    simpa [flip] using hflip u

  -- Restate the complement-pair identity using `S` and `flip`.
  have hSpair (u : Fin n → Bool) :
      S u + S (flip u) = 2 * a₀ + ∑ i, a i := by
    simpa [S, flip] using hpair u

  -- True inputs have strictly positive scores.
  have hpos (u : Fin n → Bool) (hu : f u = true) :
      0 < S u := by
    exact (hsep u).mpr hu

  -- False inputs have nonpositive scores.
  have hnonpos (u : Fin n → Bool) (hu : f u = false) :
      S u ≤ 0 := by
    apply le_of_not_gt
    intro hp
    have ht : f u = true := (hsep u).mp hp
    rw [hu] at ht
    contradiction

  -- Examine the possible output values at x and y.
  cases hx : f x <;> cases hy : f y

  -- Both outputs are false, contradicting hxy.
  · exact hxy (hx.trans hy.symm)

  -- x is false and y is true.
  · have hxsum : S x + S (flip x) ≤ 0 :=
      add_nonpos
        (hnonpos x hx)
        (hnonpos (flip x) ((hflip' x).trans hx))
    have hysum : 0 < S y + S (flip y) :=
      add_pos
        (hpos y hy)
        (hpos (flip y) ((hflip' y).trans hy))

    -- Both sums equal the same constant, producing a contradiction.
    linarith [hSpair x, hSpair y]

  -- x is true and y is false.
  · have hxsum : 0 < S x + S (flip x) :=
      add_pos
        (hpos x hx)
        (hpos (flip x) ((hflip' x).trans hx))
    have hysum : S y + S (flip y) ≤ 0 :=
      add_nonpos
        (hnonpos y hy)
        (hnonpos (flip y) ((hflip' y).trans hy))

    -- Again, both sums equal the same constant.
    linarith [hSpair x, hSpair y]

  -- Both outputs are true, contradicting hxy.
  · exact hxy (hx.trans hy.symm)

/--
A nonconstant complement-invariant Boolean function is not a linear threshold
function.
-/
theorem not_isLTF_of_complement_symmetry
    (f : (Fin n → Bool) → Bool)
    (hflip : ∀ x, f (fun i ↦ !(x i)) = f x)
    (hnonconst : ∃ x y, f x ≠ f y) :
    ¬ isLTF f := by
  intro hLTF
  exact no_affine_separator f hflip hnonconst hLTF

/--
A nonconstant complement-invariant Boolean function has threshold degree greater
than one.
-/
theorem not_thresholdDegLE_one_of_complement_symmetry
    (f : (Fin n → Bool) → Bool)
    (hflip : ∀ x, f (fun i ↦ !(x i)) = f x)
    (hnonconst : ∃ x y, f x ≠ f y) :
    ¬ ThresholdDegLE f 1 := by
  intro hdeg
  apply not_isLTF_of_complement_symmetry f hflip hnonconst
  exact (ThresholdDegLE_one_iff_isLTF f).mp hdeg

/--
Every nonconstant complement-invariant Boolean function requires at least two
attention heads.
-/
theorem HStar_ge_two_of_complement_symmetry
    (f : (Fin n → Bool) → Bool)
    (hflip : ∀ x, f (fun i ↦ !(x i)) = f x)
    (hnonconst : ∃ x y, f x ≠ f y) :
    2 ≤ HStar n f := by
  have hnotLTF :=
    not_isLTF_of_complement_symmetry f hflip hnonconst

  -- Nonconstancy rules out zero heads.
  have hne_zero : HStar n f ≠ 0 := by
    intro hzero
    rcases hnonconst with ⟨x, y, hxy⟩
    exact hxy (((HStar_eq_zero_iff f).mp hzero) x y)

  -- The affine obstruction rules out one head.
  have hne_one : HStar n f ≠ 1 := by
    intro hone
    exact hnotLTF ((HStar_eq_one_iff f).mp hone).2

  omega

end HeadComplexity
