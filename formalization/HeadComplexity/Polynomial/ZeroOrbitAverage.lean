import HeadComplexity.Results.LowComplexity

set_option linter.style.emptyLine false
set_option linter.style.whitespace false

/-!

# Zero-orbit-average symmetry obstruction

Let a finite group `G` act on an input space `X`, and let `embed : X → V` map
inputs into a real vector space. Suppose every group orbit has zero total
embedded displacement:

`∑ g : G, embed (g • x) = 0`

for every `x`. Any affine score

`S(x) = a₀ + L (embed x)`

then has the same sum over every orbit:

`∑ g : G, S(g • x) = |G| a₀`.

If a Boolean function is `G`-invariant, every point in a given orbit has the
same label. Thus an orbit labelled `true` has a strictly positive score sum,
whereas an orbit labelled `false` has a nonpositive score sum. A nonconstant
invariant function has orbits of both types, contradicting the equality of
their orbit sums. Therefore no affine separator exists.

For Boolean-cube inputs, the file uses the centered embedding

`centeredCubePoint x i = 2 * boolToReal (x i) - 1`.

It then converts an ordinary affine separator in `{0,1}` coordinates into an
affine functional of these centered coordinates. Combining the abstract orbit
obstruction with the repository's one-head characterization proves

`2 ≤ HStar n f`.

-/

namespace HeadComplexity
open scoped BigOperators

/--
The embedding of every group orbit has zero sum. Division by `|G|` is omitted
because it does not affect whether the orbit average vanishes.
-/
def HasZeroOrbitAverage
    (G X V : Type*)
    [Fintype G] [Group G] [MulAction G X]
    [AddCommGroup V]
    (embed : X → V) : Prop :=
  ∀ x, ∑ g : G, embed (g • x) = 0

/--
A nonconstant invariant Boolean function on a space with zero orbit averages
has no affine sign representation.
-/
theorem no_affine_separator_of_zero_orbit_average
    {G X V : Type*}
    [Fintype G] [Group G] [MulAction G X]
    [AddCommGroup V] [Module ℝ V]
    (embed : X → V)
    (f : X → Bool)
    (hinv : ∀ (g : G) (x : X), f (g • x) = f x)
    (hzero : HasZeroOrbitAverage G X V embed)
    (hnonconst : ∃ x y, f x ≠ f y) :
    ¬ ∃ a₀ : ℝ, ∃ L : V →ₗ[ℝ] ℝ,
      ∀ x, (0 < a₀ + L (embed x) ↔ f x = true) := by
  -- Assume that an affine sign separator exists.
  rintro ⟨a₀, L, hsep⟩

  -- Choose two inputs with different labels.
  rcases hnonconst with ⟨x, y, hxy⟩

  -- Name the affine score.
  let S : X → ℝ :=
    fun u ↦ a₀ + L (embed u)

  -- Zero orbit averages imply that every orbit has the same total score.
  have hsum (u : X) :
      ∑ g : G, S (g • u) = ∑ _g : G, a₀ := by
    simp only [S, Finset.sum_add_distrib]
    rw [← map_sum, hzero u, map_zero, add_zero]

  have hsum_eq (u v : X) :
      ∑ g : G, S (g • u) = ∑ g : G, S (g • v) := by
    exact (hsum u).trans (hsum v).symm

  -- True inputs have positive scores.
  have hpos (u : X) (hu : f u = true) :
      0 < S u := by
    simpa [S] using (hsep u).mpr hu

  -- False inputs have nonpositive scores.
  have hnonpos (u : X) (hu : f u = false) :
      S u ≤ 0 := by
    apply le_of_not_gt
    intro hp
    have ht : f u = true := (hsep u).mp (by simpa [S] using hp)
    rw [hu] at ht
    contradiction

  have horbit_pos (u : X) (hu : f u = true) :
      0 < ∑ g : G, S (g • u) := by
    apply Finset.sum_pos
    · intro g _
      exact hpos (g • u) ((hinv g u).trans hu)
    · exact ⟨1, Finset.mem_univ 1⟩

  have horbit_nonpos (u : X) (hu : f u = false) :
      (∑ g : G, S (g • u)) ≤ 0 := by
    apply Finset.sum_nonpos
    intro g _
    exact hnonpos (g • u) ((hinv g u).trans hu)

  -- The two chosen inputs have opposite labels.
  cases hx : f x <;> cases hy : f y

  -- Both labels are false, contradicting their inequality.
  · exact hxy (hx.trans hy.symm)

  -- The x-orbit is nonpositive and the y-orbit is positive, but their
  -- total scores are equal.
  · have hxsum := horbit_nonpos x hx
    have hysum := horbit_pos y hy
    linarith [hsum_eq x y]

  -- The x-orbit is positive and the y-orbit is nonpositive, but their
  -- total scores are equal.
  · have hxsum := horbit_pos x hx
    have hysum := horbit_nonpos y hy
    linarith [hsum_eq x y]

  -- Both labels are true, again contradicting their inequality.
  · exact hxy (hx.trans hy.symm)


/-- Center the Boolean cube at the origin. -/
def centeredCubePoint {n : ℕ} (x : Fin n → Bool) : Fin n → ℝ :=
  fun i ↦ 2 * boolToReal (x i) - 1

/--
A nonconstant invariant Boolean function whose centered group orbits have zero
average requires at least two attention heads.
-/
theorem HStar_ge_two_of_zero_orbit_average
    {G : Type*}
    [Fintype G] [Group G] [MulAction G (Fin n → Bool)]
    (f : (Fin n → Bool) → Bool)
    (hinv : ∀ (g : G) (x : Fin n → Bool), f (g • x) = f x)
    (hzero :
      HasZeroOrbitAverage
        G
        (Fin n → Bool)
        (Fin n → ℝ)
        centeredCubePoint)
    (hnonconst : ∃ x y, f x ≠ f y) :
    2 ≤ HStar n f := by
  have hnotLTF : ¬ isLTF f := by
    unfold isLTF
    rintro ⟨c, cs, hsep⟩

    let L : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
      {
        toFun := fun z ↦ ∑ i, (cs i / 2) * z i
        map_add' := by
          intro z w
          simp [mul_add, Finset.sum_add_distrib]
        map_smul' := by
          intro r z
          simp only [Pi.smul_apply, smul_eq_mul]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          simp only [RingHom.id_apply]
          ring
      }

    have hterm (x : Fin n → Bool) (i : Fin n) :
        cs i * boolToReal (x i)
          =
        cs i / 2 + (cs i / 2) * centeredCubePoint x i := by
      simp [centeredCubePoint]
      ring

    have hscore (x : Fin n → Bool) :
        c + ∑ i, cs i * boolToReal (x i)
          =
        (c + ∑ i, cs i / 2) + L (centeredCubePoint x) := by
      calc
        c + ∑ i, cs i * boolToReal (x i)
            =
          c + ∑ i,
            (cs i / 2 +
              (cs i / 2) * centeredCubePoint x i) := by
                apply congrArg (fun t : ℝ ↦ c + t)
                apply Finset.sum_congr rfl
                intro i _
                exact hterm x i
        _ = (c + ∑ i, cs i / 2) + L (centeredCubePoint x) := by
              simp [L, Finset.sum_add_distrib]
              ring

    apply
      no_affine_separator_of_zero_orbit_average
        centeredCubePoint f hinv hzero hnonconst

    refine ⟨c + ∑ i, cs i / 2, L, ?_⟩
    intro x
    rw [← hscore x]
    exact hsep x

  have hne_zero : HStar n f ≠ 0 := by
    intro hzeroHeads
    rcases hnonconst with ⟨x, y, hxy⟩
    exact hxy (((HStar_eq_zero_iff f).mp hzeroHeads) x y)

  have hne_one : HStar n f ≠ 1 := by
    intro hone
    exact hnotLTF ((HStar_eq_one_iff f).mp hone).2

  omega

end HeadComplexity
