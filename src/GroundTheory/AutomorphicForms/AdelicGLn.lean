module

public import Mathlib
public import GroundTheory.GlobalFields.LocalFieldAtPlace
public import GroundTheory.GlobalFields.Adele.Topology
public import GroundTheory.GlobalFields.Adele.Discrete
public import GroundTheory.GlobalFields.Adele.Bundle0002
public import GroundTheory.AutomorphicForms.GLnLocal
public import GroundTheory.AutomorphicForms.Bundle0004
public import GroundTheory.AutomorphicForms.Bundle0010

@[expose] public section

open NumberField IsDedekindDomain Topology Filter Set
open scoped NumberField.AdeleRing RestrictedProduct

namespace GroundTheory.Automorphic

noncomputable section

instance locallyCompactSpace_matrix {m R : Type*} [Finite m] [TopologicalSpace R]
    [LocallyCompactSpace R] : LocallyCompactSpace (Matrix m m R) :=
  inferInstanceAs (LocallyCompactSpace (m → m → R))

namespace AdelicGLn

variable (K : Type*) [Field K] [NumberField K] (n : ℕ)

abbrev AdelicMatrix : Type _ := Matrix (Fin n) (Fin n) 𝔸[K]

abbrev AdelicGL : Type _ := GL (Fin n) 𝔸[K]

abbrev InfiniteAdelicGL : Type _ := GL (Fin n) (InfiniteAdeleRing K)

abbrev FiniteAdelicGL : Type _ := GL (Fin n) (FiniteAdeleRing (𝓞 K) K)

instance (priority := high) locallyCompactSpace : LocallyCompactSpace (AdelicGL K n) :=
  Units.instLocallyCompactSpaceOfT1SpaceOfContinuousMul

instance (priority := high) locallyCompactSpace_finite :
    LocallyCompactSpace (FiniteAdelicGL K n) :=
  Units.instLocallyCompactSpaceOfT1SpaceOfContinuousMul

instance (priority := high) locallyCompactSpace_infinite :
    LocallyCompactSpace (InfiniteAdelicGL K n) :=
  Units.instLocallyCompactSpaceOfT1SpaceOfContinuousMul

instance (priority := high) weaklyLocallyCompactSpace :
    WeaklyLocallyCompactSpace (AdelicGL K n) :=
  instWeaklyLocallyCompactSpaceOfLocallyCompactSpace

instance (priority := high) weaklyLocallyCompactSpace_finite :
    WeaklyLocallyCompactSpace (FiniteAdelicGL K n) :=
  instWeaklyLocallyCompactSpaceOfLocallyCompactSpace

instance (priority := high) weaklyLocallyCompactSpace_infinite :
    WeaklyLocallyCompactSpace (InfiniteAdelicGL K n) :=
  instWeaklyLocallyCompactSpaceOfLocallyCompactSpace

instance (priority := high) isTopologicalGroup : IsTopologicalGroup (AdelicGL K n) :=
  Units.instIsTopologicalGroupOfContinuousMul

instance (priority := high) isTopologicalGroup_finite :
    IsTopologicalGroup (FiniteAdelicGL K n) :=
  Units.instIsTopologicalGroupOfContinuousMul

omit [NumberField K] in
instance (priority := high) isTopologicalGroup_infinite :
    IsTopologicalGroup (InfiniteAdelicGL K n) :=
  Units.instIsTopologicalGroupOfContinuousMul

instance (priority := high) t2Space : T2Space (AdelicGL K n) :=
  Units.instT2Space

instance (priority := high) t2Space_finite : T2Space (FiniteAdelicGL K n) :=
  Units.instT2Space

omit [NumberField K] in
instance (priority := high) t2Space_infinite : T2Space (InfiniteAdelicGL K n) :=
  Units.instT2Space

instance (priority := high) t1Space : T1Space (AdelicGL K n) :=
  T2Space.t1Space

instance (priority := high) t1Space_finite : T1Space (FiniteAdelicGL K n) :=
  T2Space.t1Space

omit [NumberField K] in
instance (priority := high) t1Space_infinite : T1Space (InfiniteAdelicGL K n) :=
  T2Space.t1Space

instance (priority := high) t0Space : T0Space (AdelicGL K n) :=
  T1Space.t0Space

instance (priority := high) t0Space_finite : T0Space (FiniteAdelicGL K n) :=
  T1Space.t0Space

omit [NumberField K] in
instance (priority := high) t0Space_infinite : T0Space (InfiniteAdelicGL K n) :=
  T1Space.t0Space

instance (priority := high) r1Space : R1Space (AdelicGL K n) :=
  T2Space.r1Space

instance (priority := high) r1Space_finite : R1Space (FiniteAdelicGL K n) :=
  T2Space.r1Space

omit [NumberField K] in
instance (priority := high) r1Space_infinite : R1Space (InfiniteAdelicGL K n) :=
  T2Space.r1Space

instance (priority := high) regularSpace : RegularSpace (AdelicGL K n) :=
  IsTopologicalGroup.regularSpace _

instance (priority := high) regularSpace_finite : RegularSpace (FiniteAdelicGL K n) :=
  IsTopologicalGroup.regularSpace _

omit [NumberField K] in
instance (priority := high) regularSpace_infinite : RegularSpace (InfiniteAdelicGL K n) :=
  IsTopologicalGroup.regularSpace _

instance (priority := high) t3Space : T3Space (AdelicGL K n) :=
  instT3Space

instance (priority := high) t3Space_finite : T3Space (FiniteAdelicGL K n) :=
  instT3Space

omit [NumberField K] in
instance (priority := high) t3Space_infinite : T3Space (InfiniteAdelicGL K n) :=
  instT3Space

instance (priority := high) secondCountableTopology [SecondCountableTopology 𝔸[K]] :
    SecondCountableTopology (AdelicGL K n) := by
  have : SecondCountableTopology (AdelicMatrix K n) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → 𝔸[K]))
  have : SecondCountableTopology (AdelicMatrix K n)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

instance (priority := high) secondCountableTopology_finite
    [SecondCountableTopology (FiniteAdeleRing (𝓞 K) K)] :
    SecondCountableTopology (FiniteAdelicGL K n) := by
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 K) K)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → FiniteAdeleRing (𝓞 K) K))
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 K) K))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

omit [NumberField K] in
instance (priority := high) secondCountableTopology_infinite
    [SecondCountableTopology (InfiniteAdeleRing K)] :
    SecondCountableTopology (InfiniteAdelicGL K n) := by
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → InfiniteAdeleRing K))
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) (InfiniteAdeleRing K))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

instance (priority := high) firstCountableTopology [SecondCountableTopology 𝔸[K]] :
    FirstCountableTopology (AdelicGL K n) :=
  TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _

instance (priority := high) firstCountableTopology_finite
    [SecondCountableTopology (FiniteAdeleRing (𝓞 K) K)] :
    FirstCountableTopology (FiniteAdelicGL K n) :=
  TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _

omit [NumberField K] in
instance (priority := high) firstCountableTopology_infinite
    [SecondCountableTopology (InfiniteAdeleRing K)] :
    FirstCountableTopology (InfiniteAdelicGL K n) :=
  TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _

instance (priority := high) sigmaCompactSpace [SecondCountableTopology 𝔸[K]] :
    SigmaCompactSpace (AdelicGL K n) :=
  sigmaCompactSpace_of_locallyCompact_secondCountable

instance (priority := high) sigmaCompactSpace_finite
    [SecondCountableTopology (FiniteAdeleRing (𝓞 K) K)] :
    SigmaCompactSpace (FiniteAdelicGL K n) :=
  sigmaCompactSpace_of_locallyCompact_secondCountable

instance (priority := high) sigmaCompactSpace_infinite
    [SecondCountableTopology (InfiniteAdeleRing K)] :
    SigmaCompactSpace (InfiniteAdelicGL K n) :=
  sigmaCompactSpace_of_locallyCompact_secondCountable

def det : AdelicGL K n →* (𝔸[K])ˣ :=
  Matrix.GeneralLinearGroup.det

@[simp]
theorem coe_det (g : AdelicGL K n) : (det K n g : 𝔸[K]) = (g : AdelicMatrix K n).det :=
  rfl

theorem continuous_det : Continuous (det K n) := by
  refine Units.continuous_iff.2 ⟨Continuous.matrix_det (Units.continuous_val (M := AdelicMatrix K n)),
    ?_⟩
  have : (fun g : AdelicGL K n => (((det K n g)⁻¹ : (𝔸[K])ˣ) : 𝔸[K])) =
      fun g => ((g⁻¹ : AdelicGL K n) : AdelicMatrix K n).det := by
    funext g
    rw [← map_inv]
    rfl
  rw [this]
  exact Continuous.matrix_det (Units.continuous_coe_inv (M := AdelicMatrix K n))

def prodEquiv : AdelicGL K n ≃ₜ* InfiniteAdelicGL K n × FiniteAdelicGL K n :=
  glProdEquiv (Fin n) (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)

@[simp]
theorem prodEquiv_apply_fst (g : AdelicGL K n) (a b : Fin n) :
    (prodEquiv K n g).1 a b = (g a b).1 :=
  rfl

@[simp]
theorem prodEquiv_apply_snd (g : AdelicGL K n) (a b : Fin n) :
    (prodEquiv K n g).2 a b = (g a b).2 :=
  rfl

def infiniteEquiv : InfiniteAdelicGL K n ≃ₜ* Π w : InfinitePlace K, GL (Fin n) w.Completion :=
  glPiEquiv (Fin n) fun w : InfinitePlace K => w.Completion

omit [NumberField K] in
@[simp]
theorem infiniteEquiv_apply (g : InfiniteAdelicGL K n) (w : InfinitePlace K) (a b : Fin n) :
    infiniteEquiv K n g w a b = g a b w :=
  rfl

theorem mem_integralMatrices_adicCompletion (v : HeightOneSpectrum (𝓞 K))
    (M : Matrix (Fin n) (Fin n) (v.adicCompletion K)) :
    M ∈ GLnLocal.integralMatrices (v.adicCompletion K) n ↔
      ∀ a b, M a b ∈ v.adicCompletionIntegers K := by
  rw [GLnLocal.mem_integralMatrices]
  simp only [GroundTheory.Global.mem_valuationInteger_iff]

def finiteRestrictedEquiv :
    FiniteAdelicGL K n ≃ₜ* Πʳ v : HeightOneSpectrum (𝓞 K),
      [GL (Fin n) (v.adicCompletion K), GLnLocal.integralGL (v.adicCompletion K) n] :=
  (RestrictedProduct.matrixUnitsEquiv (Fin n)
    (R := fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
    (B := fun v => v.adicCompletionIntegers K)
    (C := fun v => GLnLocal.integralMatrices (v.adicCompletion K) n)
    (mem_integralMatrices_adicCompletion K n)
    (fun v => Valued.isOpen_valuationSubring (v.adicCompletion K))).trans
    (RestrictedProduct.congrSetsMul fun v => by
      rw [GLnLocal.integralGL_eq_units]
      rfl)

@[simp]
theorem finiteRestrictedEquiv_apply (g : FiniteAdelicGL K n) (v : HeightOneSpectrum (𝓞 K))
    (a b : Fin n) :
    (finiteRestrictedEquiv K n g v : GL (Fin n) (v.adicCompletion K)) a b = g a b v :=
  rfl

def restrictedProductEquiv :
    AdelicGL K n ≃ₜ* (Π w : InfinitePlace K, GL (Fin n) w.Completion) ×
      Πʳ v : HeightOneSpectrum (𝓞 K),
        [GL (Fin n) (v.adicCompletion K), GLnLocal.integralGL (v.adicCompletion K) n] :=
  (prodEquiv K n).trans
    { toMulEquiv := MulEquiv.prodCongr (infiniteEquiv K n).toMulEquiv
        (finiteRestrictedEquiv K n).toMulEquiv
      continuous_toFun := ((infiniteEquiv K n).continuous.comp continuous_fst).prodMk
        ((finiteRestrictedEquiv K n).continuous.comp continuous_snd)
      continuous_invFun := ((infiniteEquiv K n).symm.continuous.comp continuous_fst).prodMk
        ((finiteRestrictedEquiv K n).symm.continuous.comp continuous_snd) }

theorem eventually_mem_integralGL (g : AdelicGL K n) :
    ∀ᶠ v in cofinite, (restrictedProductEquiv K n g).2 v ∈
      GLnLocal.integralGL (v.adicCompletion K) n :=
  ((restrictedProductEquiv K n g).2).2

def integralFiniteMatrices : Subring (Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 K) K)) :=
  (RingHom.mapMatrix (GroundTheory.Global.integralFiniteAdeles (𝓞 K) K).subtype).range

theorem mem_integralFiniteMatrices {M : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 K) K)} :
    M ∈ integralFiniteMatrices K n ↔
      ∀ a b, M a b ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K := by
  constructor
  · rintro ⟨N, rfl⟩ a b
    exact (N a b).2
  · intro h
    exact ⟨Matrix.of fun a b => ⟨M a b, h a b⟩, rfl⟩

def integralFiniteGL : Subgroup (FiniteAdelicGL K n) :=
  (integralFiniteMatrices K n).toSubmonoid.units

theorem mem_integralFiniteGL_iff {g : FiniteAdelicGL K n} :
    g ∈ integralFiniteGL K n ↔
      (∀ a b, g a b ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K) ∧
        ∀ a b, (g⁻¹ : FiniteAdelicGL K n) a b ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K := by
  rw [integralFiniteGL, Submonoid.mem_units_iff, Subring.mem_toSubmonoid,
    Subring.mem_toSubmonoid, mem_integralFiniteMatrices, mem_integralFiniteMatrices]

theorem mem_integralFiniteGL_iff_forall {g : FiniteAdelicGL K n} :
    g ∈ integralFiniteGL K n ↔
      ∀ v, finiteRestrictedEquiv K n g v ∈ GLnLocal.integralGL (v.adicCompletion K) n := by
  have hinv : ∀ v a b, ((finiteRestrictedEquiv K n g v)⁻¹ : GL (Fin n) (v.adicCompletion K)) a b =
      (g⁻¹ : FiniteAdelicGL K n) a b v := fun v a b => by
    rw [← RestrictedProduct.inv_apply, ← map_inv]
    rfl
  simp only [mem_integralFiniteGL_iff, GLnLocal.mem_integralGL_iff, hinv,
    finiteRestrictedEquiv_apply, GroundTheory.Global.mem_valuationInteger_iff,
    GroundTheory.Global.mem_integralFiniteAdeles]
  constructor
  · rintro ⟨h1, h2⟩ v
    exact ⟨fun a b => h1 a b v, fun a b => h2 a b v⟩
  · intro h
    exact ⟨fun a b v => (h v).1 a b, fun a b v => (h v).2 a b⟩

theorem isOpen_integralFiniteMatrices :
    IsOpen (integralFiniteMatrices K n : Set (Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 K) K))) := by
  have : (integralFiniteMatrices K n : Set (Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 K) K))) =
      ⋂ a, ⋂ b, (fun M : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 K) K) => M a b) ⁻¹'
        (GroundTheory.Global.integralFiniteAdeles (𝓞 K) K) := by
    ext M
    simp [mem_integralFiniteMatrices]
  rw [this]
  exact isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b =>
    GroundTheory.Global.isOpen_integralFiniteAdeles.preimage (continuous_apply_apply a b)

theorem isCompact_integralFiniteMatrices :
    IsCompact (integralFiniteMatrices K n :
      Set (Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 K) K))) := by
  have : (integralFiniteMatrices K n : Set (Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 K) K))) =
      Set.pi univ fun _ => Set.pi univ fun _ =>
        (GroundTheory.Global.integralFiniteAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K)) := by
    exact Set.ext fun M =>
      ⟨fun h a _ b _ => (mem_integralFiniteMatrices K n).1 h a b,
        fun h => (mem_integralFiniteMatrices K n).2 fun a b => h a (mem_univ a) b (mem_univ b)⟩
  rw [this]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
    GroundTheory.Global.isCompact_integralFiniteAdeles K

theorem isOpen_integralFiniteGL : IsOpen (integralFiniteGL K n : Set (FiniteAdelicGL K n)) :=
  Submonoid.isOpen_units (isOpen_integralFiniteMatrices K n)

theorem isCompact_integralFiniteGL :
    IsCompact (integralFiniteGL K n : Set (FiniteAdelicGL K n)) := by
  have h := (isCompact_integralFiniteMatrices K n).prod
    (MulOpposite.opHomeomorph.symm.isCompact_preimage.2 (isCompact_integralFiniteMatrices K n))
  convert Units.isClosedEmbedding_embedProduct.isCompact_preimage h using 1
  ext u
  simp only [SetLike.mem_coe, integralFiniteGL, Submonoid.mem_units_iff, Set.mem_preimage,
    Set.mem_prod, Units.embedProduct_apply, Subring.mem_toSubmonoid]
  exact Iff.rfl

theorem totallyDisconnectedSpace_of_injective {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TotallyDisconnectedSpace Y] {f : X → Y} (hf : Continuous f)
    (hinj : Function.Injective f) : TotallyDisconnectedSpace X :=
  ⟨fun s _ hs => Set.subsingleton_of_image hinj s
    (isTotallyDisconnected_of_totallyDisconnectedSpace _ _ (Set.subset_univ _)
      (hs.image f hf.continuousOn))⟩

instance totallyDisconnectedSpace_finite : TotallyDisconnectedSpace (FiniteAdelicGL K n) :=
  totallyDisconnectedSpace_of_injective
    (f := fun g v => finiteRestrictedEquiv K n g v)
    (continuous_pi fun v =>
      (_root_.RestrictedProduct.continuous_eval v).comp (finiteRestrictedEquiv K n).continuous)
    fun _ _ hgh => (finiteRestrictedEquiv K n).injective
      (Subtype.ext (funext fun v => congrFun hgh v))

theorem finite_hasBasis_nhds_one :
    (𝓝 (1 : FiniteAdelicGL K n)).HasBasis
      (fun H : OpenSubgroup (FiniteAdelicGL K n) => IsCompact (H : Set (FiniteAdelicGL K n)))
      fun H => (H : Set (FiniteAdelicGL K n)) :=
  hasBasis_nhds_one_compactOpenSubgroup

def diagonal : GL (Fin n) K →* AdelicGL K n :=
  Units.map (algebraMap K 𝔸[K]).mapMatrix.toMonoidHom

@[simp]
theorem diagonal_apply (γ : GL (Fin n) K) (a b : Fin n) :
    diagonal K n γ a b = algebraMap K 𝔸[K] (γ a b) :=
  rfl

theorem diagonal_injective : Function.Injective (diagonal K n) := fun _ _ h =>
  Units.ext <| Matrix.ext fun a b =>
    NumberField.AdeleRing.algebraMap_injective (𝓞 K) K (congrArg (fun g : AdelicGL K n => g a b) h)

def rationalGL : Subgroup (AdelicGL K n) :=
  (diagonal K n).range

theorem exists_isOpen_inter_eq_zero :
    ∃ V : Set 𝔸[K], IsOpen V ∧ (0 : 𝔸[K]) ∈ V ∧ ∀ k : K, algebraMap K 𝔸[K] k ∈ V → k = 0 := by
  have := GroundTheory.Global.discreteTopology_principalSubgroup K
  obtain ⟨V, hVo, hV⟩ := isOpen_induced_iff.1
    (isOpen_discrete ({0} : Set (NumberField.AdeleRing.principalSubgroup (𝓞 K) K)))
  refine ⟨V, hVo, ?_, fun k hk => ?_⟩
  · have : (0 : NumberField.AdeleRing.principalSubgroup (𝓞 K) K) ∈ Subtype.val ⁻¹' V := by
      rw [hV]; rfl
    exact this
  · have : (⟨algebraMap K 𝔸[K] k, ⟨k, rfl⟩⟩ : NumberField.AdeleRing.principalSubgroup (𝓞 K) K) ∈
        Subtype.val ⁻¹' V := hk
    rw [hV, Set.mem_singleton_iff, Subtype.ext_iff] at this
    exact NumberField.AdeleRing.algebraMap_injective (𝓞 K) K (this.trans (map_zero _).symm)

theorem discreteTopology_rationalGL : DiscreteTopology (rationalGL K n) := by
  obtain ⟨V, hVo, hV0, hV⟩ := exists_isOpen_inter_eq_zero K
  let W : Set (AdelicGL K n) :=
    ⋂ a, ⋂ b, (fun g : AdelicGL K n => (g : AdelicMatrix K n) a b - (1 : AdelicMatrix K n) a b) ⁻¹' V
  have hWo : IsOpen W := isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b =>
    hVo.preimage
      ((Continuous.matrix_elem (Units.continuous_val (M := AdelicMatrix K n)) a b).sub
        continuous_const)
  refine discreteTopology_of_isOpen_singleton_one (isOpen_induced_iff.2 ⟨W, hWo, ?_⟩)
  ext ⟨g, γ, rfl⟩
  simp only [W, Set.mem_preimage, Set.mem_iInter, Set.mem_singleton_iff]
  constructor
  · intro h
    have hγ : γ = 1 := by
      have hsub : ((diagonal K n γ : AdelicGL K n) : AdelicMatrix K n) - 1 =
          (algebraMap K 𝔸[K]).mapMatrix ((γ : Matrix (Fin n) (Fin n) K) - 1) := by
        rw [map_sub, map_one]
        rfl
      refine Units.ext <| Matrix.ext fun a b => ?_
      have h1 := h a b
      rw [← Matrix.sub_apply, hsub] at h1
      have h2 := hV _ h1
      rw [Matrix.sub_apply, sub_eq_zero] at h2
      exact h2
    subst hγ
    exact Subtype.ext (map_one _)
  · intro h a b
    have : (diagonal K n γ : AdelicGL K n) = 1 := congrArg Subtype.val h
    rw [this, Units.val_one, sub_self]
    exact hV0

theorem isClosed_rationalGL : IsClosed (rationalGL K n : Set (AdelicGL K n)) :=
  have := discreteTopology_rationalGL K n
  by
    set_option synthInstance.maxHeartbeats 200000 in
      exact Subgroup.isClosed_of_discrete

end AdelicGLn

end

end GroundTheory.Automorphic
