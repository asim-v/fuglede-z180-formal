import Fuglede.Z180K30ExceptionalProjectiveProfileD6CompletenessFallbackB00V97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6CompletenessFallbackB01V97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6CompletenessFallbackB02V97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6CompletenessFallbackB03V97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6CompletenessFallbackB04V97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6CompletenessFallbackB05V97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6CompletenessFallbackB06V97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6CompletenessFallbackB07V97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6CompletenessFallbackB08V97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6CompletenessFallbackB09V97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6CompletenessFallbackB10V97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6CompletenessFallbackB11V97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6CompletenessFallbackB12V97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6CompletenessFallbackB13V97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6CompletenessFallbackB14V97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6CompletenessFallbackB15V97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6CompletenessFallbackB16V97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6CompletenessFallbackB17V97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6CompletenessFallbackB18V97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6CompletenessFallbackB19V97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6CompletenessFallbackB20V97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6CompletenessFallbackB21V97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6CompletenessFallbackB22V97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6CompletenessFallbackB23V97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6CompletenessFallbackB24V97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6CompletenessFallbackB25V97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6CompletenessFallbackB26V97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6CompletenessFallbackB27V97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6CompletenessFallbackB28V97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6CompletenessFallbackB29V97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6CompletenessFallbackB30V97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6CompletenessFallbackB31V97

/-! Structural replay of the 32 isolated D6 completeness buckets. -/

namespace Fuglede.Z180K30ExceptionalRawV2

theorem z180_k30_projective_u_profile_members_complete_fallback_v97_d6 :
    z180K30ProjectiveD6FallbackSourceGroupedV97.Perm
      normalizedProjectiveUniqueUChoicesV89 6 := by
  have hSource31 :
      z180K30ProjectiveD6FallbackSourceTailV97B31.Perm z180K30ProjectiveD6FallbackSourceRemainderV97B31 := by
    rfl
  have hTarget31 :
      z180K30ProjectiveD6FallbackTargetTailV97B31.Perm z180K30ProjectiveD6FallbackTargetRemainderV97B31 := by
    rfl
  have hBuckets31 :
      z180K30ProjectiveD6FallbackSourceTailV97B31.Perm z180K30ProjectiveD6FallbackTargetTailV97B31 := by
    exact z180_k30_projective_d6_fallback_bucket_v97_b31
  have hSourceSplit30 :
      (z180K30ProjectiveD6FallbackSourceBucketV97B30 ++ z180K30ProjectiveD6FallbackSourceRemainderV97B31).Perm
        z180K30ProjectiveD6FallbackSourceRemainderV97B30 := by
    simpa only [z180K30ProjectiveD6FallbackSourceBucketV97B30, z180K30ProjectiveD6FallbackSourceRemainderV97B31] using
      (List.filter_append_perm
        (z180K30ProjectiveD6FallbackPredicateV97 30)
        z180K30ProjectiveD6FallbackSourceRemainderV97B30)
  have hTargetSplit30 :
      (z180K30ProjectiveD6FallbackTargetBucketV97B30 ++ z180K30ProjectiveD6FallbackTargetRemainderV97B31).Perm
        z180K30ProjectiveD6FallbackTargetRemainderV97B30 := by
    simpa only [z180K30ProjectiveD6FallbackTargetBucketV97B30, z180K30ProjectiveD6FallbackTargetRemainderV97B31] using
      (List.filter_append_perm
        (z180K30ProjectiveD6FallbackPredicateV97 30)
        z180K30ProjectiveD6FallbackTargetRemainderV97B30)
  have hSource30 :
      z180K30ProjectiveD6FallbackSourceTailV97B30.Perm z180K30ProjectiveD6FallbackSourceRemainderV97B30 := by
    change (z180K30ProjectiveD6FallbackSourceBucketV97B30 ++ z180K30ProjectiveD6FallbackSourceTailV97B31).Perm _
    exact
      ((List.Perm.refl z180K30ProjectiveD6FallbackSourceBucketV97B30).append hSource31).trans
        hSourceSplit30
  have hTarget30 :
      z180K30ProjectiveD6FallbackTargetTailV97B30.Perm z180K30ProjectiveD6FallbackTargetRemainderV97B30 := by
    change (z180K30ProjectiveD6FallbackTargetBucketV97B30 ++ z180K30ProjectiveD6FallbackTargetTailV97B31).Perm _
    exact
      ((List.Perm.refl z180K30ProjectiveD6FallbackTargetBucketV97B30).append hTarget31).trans
        hTargetSplit30
  have hBuckets30 :
      z180K30ProjectiveD6FallbackSourceTailV97B30.Perm z180K30ProjectiveD6FallbackTargetTailV97B30 := by
    change (z180K30ProjectiveD6FallbackSourceBucketV97B30 ++ z180K30ProjectiveD6FallbackSourceTailV97B31).Perm
      (z180K30ProjectiveD6FallbackTargetBucketV97B30 ++ z180K30ProjectiveD6FallbackTargetTailV97B31)
    exact
      z180_k30_projective_d6_fallback_bucket_v97_b30.append hBuckets31
  have hSourceSplit29 :
      (z180K30ProjectiveD6FallbackSourceBucketV97B29 ++ z180K30ProjectiveD6FallbackSourceRemainderV97B30).Perm
        z180K30ProjectiveD6FallbackSourceRemainderV97B29 := by
    simpa only [z180K30ProjectiveD6FallbackSourceBucketV97B29, z180K30ProjectiveD6FallbackSourceRemainderV97B30] using
      (List.filter_append_perm
        (z180K30ProjectiveD6FallbackPredicateV97 29)
        z180K30ProjectiveD6FallbackSourceRemainderV97B29)
  have hTargetSplit29 :
      (z180K30ProjectiveD6FallbackTargetBucketV97B29 ++ z180K30ProjectiveD6FallbackTargetRemainderV97B30).Perm
        z180K30ProjectiveD6FallbackTargetRemainderV97B29 := by
    simpa only [z180K30ProjectiveD6FallbackTargetBucketV97B29, z180K30ProjectiveD6FallbackTargetRemainderV97B30] using
      (List.filter_append_perm
        (z180K30ProjectiveD6FallbackPredicateV97 29)
        z180K30ProjectiveD6FallbackTargetRemainderV97B29)
  have hSource29 :
      z180K30ProjectiveD6FallbackSourceTailV97B29.Perm z180K30ProjectiveD6FallbackSourceRemainderV97B29 := by
    change (z180K30ProjectiveD6FallbackSourceBucketV97B29 ++ z180K30ProjectiveD6FallbackSourceTailV97B30).Perm _
    exact
      ((List.Perm.refl z180K30ProjectiveD6FallbackSourceBucketV97B29).append hSource30).trans
        hSourceSplit29
  have hTarget29 :
      z180K30ProjectiveD6FallbackTargetTailV97B29.Perm z180K30ProjectiveD6FallbackTargetRemainderV97B29 := by
    change (z180K30ProjectiveD6FallbackTargetBucketV97B29 ++ z180K30ProjectiveD6FallbackTargetTailV97B30).Perm _
    exact
      ((List.Perm.refl z180K30ProjectiveD6FallbackTargetBucketV97B29).append hTarget30).trans
        hTargetSplit29
  have hBuckets29 :
      z180K30ProjectiveD6FallbackSourceTailV97B29.Perm z180K30ProjectiveD6FallbackTargetTailV97B29 := by
    change (z180K30ProjectiveD6FallbackSourceBucketV97B29 ++ z180K30ProjectiveD6FallbackSourceTailV97B30).Perm
      (z180K30ProjectiveD6FallbackTargetBucketV97B29 ++ z180K30ProjectiveD6FallbackTargetTailV97B30)
    exact
      z180_k30_projective_d6_fallback_bucket_v97_b29.append hBuckets30
  have hSourceSplit28 :
      (z180K30ProjectiveD6FallbackSourceBucketV97B28 ++ z180K30ProjectiveD6FallbackSourceRemainderV97B29).Perm
        z180K30ProjectiveD6FallbackSourceRemainderV97B28 := by
    simpa only [z180K30ProjectiveD6FallbackSourceBucketV97B28, z180K30ProjectiveD6FallbackSourceRemainderV97B29] using
      (List.filter_append_perm
        (z180K30ProjectiveD6FallbackPredicateV97 28)
        z180K30ProjectiveD6FallbackSourceRemainderV97B28)
  have hTargetSplit28 :
      (z180K30ProjectiveD6FallbackTargetBucketV97B28 ++ z180K30ProjectiveD6FallbackTargetRemainderV97B29).Perm
        z180K30ProjectiveD6FallbackTargetRemainderV97B28 := by
    simpa only [z180K30ProjectiveD6FallbackTargetBucketV97B28, z180K30ProjectiveD6FallbackTargetRemainderV97B29] using
      (List.filter_append_perm
        (z180K30ProjectiveD6FallbackPredicateV97 28)
        z180K30ProjectiveD6FallbackTargetRemainderV97B28)
  have hSource28 :
      z180K30ProjectiveD6FallbackSourceTailV97B28.Perm z180K30ProjectiveD6FallbackSourceRemainderV97B28 := by
    change (z180K30ProjectiveD6FallbackSourceBucketV97B28 ++ z180K30ProjectiveD6FallbackSourceTailV97B29).Perm _
    exact
      ((List.Perm.refl z180K30ProjectiveD6FallbackSourceBucketV97B28).append hSource29).trans
        hSourceSplit28
  have hTarget28 :
      z180K30ProjectiveD6FallbackTargetTailV97B28.Perm z180K30ProjectiveD6FallbackTargetRemainderV97B28 := by
    change (z180K30ProjectiveD6FallbackTargetBucketV97B28 ++ z180K30ProjectiveD6FallbackTargetTailV97B29).Perm _
    exact
      ((List.Perm.refl z180K30ProjectiveD6FallbackTargetBucketV97B28).append hTarget29).trans
        hTargetSplit28
  have hBuckets28 :
      z180K30ProjectiveD6FallbackSourceTailV97B28.Perm z180K30ProjectiveD6FallbackTargetTailV97B28 := by
    change (z180K30ProjectiveD6FallbackSourceBucketV97B28 ++ z180K30ProjectiveD6FallbackSourceTailV97B29).Perm
      (z180K30ProjectiveD6FallbackTargetBucketV97B28 ++ z180K30ProjectiveD6FallbackTargetTailV97B29)
    exact
      z180_k30_projective_d6_fallback_bucket_v97_b28.append hBuckets29
  have hSourceSplit27 :
      (z180K30ProjectiveD6FallbackSourceBucketV97B27 ++ z180K30ProjectiveD6FallbackSourceRemainderV97B28).Perm
        z180K30ProjectiveD6FallbackSourceRemainderV97B27 := by
    simpa only [z180K30ProjectiveD6FallbackSourceBucketV97B27, z180K30ProjectiveD6FallbackSourceRemainderV97B28] using
      (List.filter_append_perm
        (z180K30ProjectiveD6FallbackPredicateV97 27)
        z180K30ProjectiveD6FallbackSourceRemainderV97B27)
  have hTargetSplit27 :
      (z180K30ProjectiveD6FallbackTargetBucketV97B27 ++ z180K30ProjectiveD6FallbackTargetRemainderV97B28).Perm
        z180K30ProjectiveD6FallbackTargetRemainderV97B27 := by
    simpa only [z180K30ProjectiveD6FallbackTargetBucketV97B27, z180K30ProjectiveD6FallbackTargetRemainderV97B28] using
      (List.filter_append_perm
        (z180K30ProjectiveD6FallbackPredicateV97 27)
        z180K30ProjectiveD6FallbackTargetRemainderV97B27)
  have hSource27 :
      z180K30ProjectiveD6FallbackSourceTailV97B27.Perm z180K30ProjectiveD6FallbackSourceRemainderV97B27 := by
    change (z180K30ProjectiveD6FallbackSourceBucketV97B27 ++ z180K30ProjectiveD6FallbackSourceTailV97B28).Perm _
    exact
      ((List.Perm.refl z180K30ProjectiveD6FallbackSourceBucketV97B27).append hSource28).trans
        hSourceSplit27
  have hTarget27 :
      z180K30ProjectiveD6FallbackTargetTailV97B27.Perm z180K30ProjectiveD6FallbackTargetRemainderV97B27 := by
    change (z180K30ProjectiveD6FallbackTargetBucketV97B27 ++ z180K30ProjectiveD6FallbackTargetTailV97B28).Perm _
    exact
      ((List.Perm.refl z180K30ProjectiveD6FallbackTargetBucketV97B27).append hTarget28).trans
        hTargetSplit27
  have hBuckets27 :
      z180K30ProjectiveD6FallbackSourceTailV97B27.Perm z180K30ProjectiveD6FallbackTargetTailV97B27 := by
    change (z180K30ProjectiveD6FallbackSourceBucketV97B27 ++ z180K30ProjectiveD6FallbackSourceTailV97B28).Perm
      (z180K30ProjectiveD6FallbackTargetBucketV97B27 ++ z180K30ProjectiveD6FallbackTargetTailV97B28)
    exact
      z180_k30_projective_d6_fallback_bucket_v97_b27.append hBuckets28
  have hSourceSplit26 :
      (z180K30ProjectiveD6FallbackSourceBucketV97B26 ++ z180K30ProjectiveD6FallbackSourceRemainderV97B27).Perm
        z180K30ProjectiveD6FallbackSourceRemainderV97B26 := by
    simpa only [z180K30ProjectiveD6FallbackSourceBucketV97B26, z180K30ProjectiveD6FallbackSourceRemainderV97B27] using
      (List.filter_append_perm
        (z180K30ProjectiveD6FallbackPredicateV97 26)
        z180K30ProjectiveD6FallbackSourceRemainderV97B26)
  have hTargetSplit26 :
      (z180K30ProjectiveD6FallbackTargetBucketV97B26 ++ z180K30ProjectiveD6FallbackTargetRemainderV97B27).Perm
        z180K30ProjectiveD6FallbackTargetRemainderV97B26 := by
    simpa only [z180K30ProjectiveD6FallbackTargetBucketV97B26, z180K30ProjectiveD6FallbackTargetRemainderV97B27] using
      (List.filter_append_perm
        (z180K30ProjectiveD6FallbackPredicateV97 26)
        z180K30ProjectiveD6FallbackTargetRemainderV97B26)
  have hSource26 :
      z180K30ProjectiveD6FallbackSourceTailV97B26.Perm z180K30ProjectiveD6FallbackSourceRemainderV97B26 := by
    change (z180K30ProjectiveD6FallbackSourceBucketV97B26 ++ z180K30ProjectiveD6FallbackSourceTailV97B27).Perm _
    exact
      ((List.Perm.refl z180K30ProjectiveD6FallbackSourceBucketV97B26).append hSource27).trans
        hSourceSplit26
  have hTarget26 :
      z180K30ProjectiveD6FallbackTargetTailV97B26.Perm z180K30ProjectiveD6FallbackTargetRemainderV97B26 := by
    change (z180K30ProjectiveD6FallbackTargetBucketV97B26 ++ z180K30ProjectiveD6FallbackTargetTailV97B27).Perm _
    exact
      ((List.Perm.refl z180K30ProjectiveD6FallbackTargetBucketV97B26).append hTarget27).trans
        hTargetSplit26
  have hBuckets26 :
      z180K30ProjectiveD6FallbackSourceTailV97B26.Perm z180K30ProjectiveD6FallbackTargetTailV97B26 := by
    change (z180K30ProjectiveD6FallbackSourceBucketV97B26 ++ z180K30ProjectiveD6FallbackSourceTailV97B27).Perm
      (z180K30ProjectiveD6FallbackTargetBucketV97B26 ++ z180K30ProjectiveD6FallbackTargetTailV97B27)
    exact
      z180_k30_projective_d6_fallback_bucket_v97_b26.append hBuckets27
  have hSourceSplit25 :
      (z180K30ProjectiveD6FallbackSourceBucketV97B25 ++ z180K30ProjectiveD6FallbackSourceRemainderV97B26).Perm
        z180K30ProjectiveD6FallbackSourceRemainderV97B25 := by
    simpa only [z180K30ProjectiveD6FallbackSourceBucketV97B25, z180K30ProjectiveD6FallbackSourceRemainderV97B26] using
      (List.filter_append_perm
        (z180K30ProjectiveD6FallbackPredicateV97 25)
        z180K30ProjectiveD6FallbackSourceRemainderV97B25)
  have hTargetSplit25 :
      (z180K30ProjectiveD6FallbackTargetBucketV97B25 ++ z180K30ProjectiveD6FallbackTargetRemainderV97B26).Perm
        z180K30ProjectiveD6FallbackTargetRemainderV97B25 := by
    simpa only [z180K30ProjectiveD6FallbackTargetBucketV97B25, z180K30ProjectiveD6FallbackTargetRemainderV97B26] using
      (List.filter_append_perm
        (z180K30ProjectiveD6FallbackPredicateV97 25)
        z180K30ProjectiveD6FallbackTargetRemainderV97B25)
  have hSource25 :
      z180K30ProjectiveD6FallbackSourceTailV97B25.Perm z180K30ProjectiveD6FallbackSourceRemainderV97B25 := by
    change (z180K30ProjectiveD6FallbackSourceBucketV97B25 ++ z180K30ProjectiveD6FallbackSourceTailV97B26).Perm _
    exact
      ((List.Perm.refl z180K30ProjectiveD6FallbackSourceBucketV97B25).append hSource26).trans
        hSourceSplit25
  have hTarget25 :
      z180K30ProjectiveD6FallbackTargetTailV97B25.Perm z180K30ProjectiveD6FallbackTargetRemainderV97B25 := by
    change (z180K30ProjectiveD6FallbackTargetBucketV97B25 ++ z180K30ProjectiveD6FallbackTargetTailV97B26).Perm _
    exact
      ((List.Perm.refl z180K30ProjectiveD6FallbackTargetBucketV97B25).append hTarget26).trans
        hTargetSplit25
  have hBuckets25 :
      z180K30ProjectiveD6FallbackSourceTailV97B25.Perm z180K30ProjectiveD6FallbackTargetTailV97B25 := by
    change (z180K30ProjectiveD6FallbackSourceBucketV97B25 ++ z180K30ProjectiveD6FallbackSourceTailV97B26).Perm
      (z180K30ProjectiveD6FallbackTargetBucketV97B25 ++ z180K30ProjectiveD6FallbackTargetTailV97B26)
    exact
      z180_k30_projective_d6_fallback_bucket_v97_b25.append hBuckets26
  have hSourceSplit24 :
      (z180K30ProjectiveD6FallbackSourceBucketV97B24 ++ z180K30ProjectiveD6FallbackSourceRemainderV97B25).Perm
        z180K30ProjectiveD6FallbackSourceRemainderV97B24 := by
    simpa only [z180K30ProjectiveD6FallbackSourceBucketV97B24, z180K30ProjectiveD6FallbackSourceRemainderV97B25] using
      (List.filter_append_perm
        (z180K30ProjectiveD6FallbackPredicateV97 24)
        z180K30ProjectiveD6FallbackSourceRemainderV97B24)
  have hTargetSplit24 :
      (z180K30ProjectiveD6FallbackTargetBucketV97B24 ++ z180K30ProjectiveD6FallbackTargetRemainderV97B25).Perm
        z180K30ProjectiveD6FallbackTargetRemainderV97B24 := by
    simpa only [z180K30ProjectiveD6FallbackTargetBucketV97B24, z180K30ProjectiveD6FallbackTargetRemainderV97B25] using
      (List.filter_append_perm
        (z180K30ProjectiveD6FallbackPredicateV97 24)
        z180K30ProjectiveD6FallbackTargetRemainderV97B24)
  have hSource24 :
      z180K30ProjectiveD6FallbackSourceTailV97B24.Perm z180K30ProjectiveD6FallbackSourceRemainderV97B24 := by
    change (z180K30ProjectiveD6FallbackSourceBucketV97B24 ++ z180K30ProjectiveD6FallbackSourceTailV97B25).Perm _
    exact
      ((List.Perm.refl z180K30ProjectiveD6FallbackSourceBucketV97B24).append hSource25).trans
        hSourceSplit24
  have hTarget24 :
      z180K30ProjectiveD6FallbackTargetTailV97B24.Perm z180K30ProjectiveD6FallbackTargetRemainderV97B24 := by
    change (z180K30ProjectiveD6FallbackTargetBucketV97B24 ++ z180K30ProjectiveD6FallbackTargetTailV97B25).Perm _
    exact
      ((List.Perm.refl z180K30ProjectiveD6FallbackTargetBucketV97B24).append hTarget25).trans
        hTargetSplit24
  have hBuckets24 :
      z180K30ProjectiveD6FallbackSourceTailV97B24.Perm z180K30ProjectiveD6FallbackTargetTailV97B24 := by
    change (z180K30ProjectiveD6FallbackSourceBucketV97B24 ++ z180K30ProjectiveD6FallbackSourceTailV97B25).Perm
      (z180K30ProjectiveD6FallbackTargetBucketV97B24 ++ z180K30ProjectiveD6FallbackTargetTailV97B25)
    exact
      z180_k30_projective_d6_fallback_bucket_v97_b24.append hBuckets25
  have hSourceSplit23 :
      (z180K30ProjectiveD6FallbackSourceBucketV97B23 ++ z180K30ProjectiveD6FallbackSourceRemainderV97B24).Perm
        z180K30ProjectiveD6FallbackSourceRemainderV97B23 := by
    simpa only [z180K30ProjectiveD6FallbackSourceBucketV97B23, z180K30ProjectiveD6FallbackSourceRemainderV97B24] using
      (List.filter_append_perm
        (z180K30ProjectiveD6FallbackPredicateV97 23)
        z180K30ProjectiveD6FallbackSourceRemainderV97B23)
  have hTargetSplit23 :
      (z180K30ProjectiveD6FallbackTargetBucketV97B23 ++ z180K30ProjectiveD6FallbackTargetRemainderV97B24).Perm
        z180K30ProjectiveD6FallbackTargetRemainderV97B23 := by
    simpa only [z180K30ProjectiveD6FallbackTargetBucketV97B23, z180K30ProjectiveD6FallbackTargetRemainderV97B24] using
      (List.filter_append_perm
        (z180K30ProjectiveD6FallbackPredicateV97 23)
        z180K30ProjectiveD6FallbackTargetRemainderV97B23)
  have hSource23 :
      z180K30ProjectiveD6FallbackSourceTailV97B23.Perm z180K30ProjectiveD6FallbackSourceRemainderV97B23 := by
    change (z180K30ProjectiveD6FallbackSourceBucketV97B23 ++ z180K30ProjectiveD6FallbackSourceTailV97B24).Perm _
    exact
      ((List.Perm.refl z180K30ProjectiveD6FallbackSourceBucketV97B23).append hSource24).trans
        hSourceSplit23
  have hTarget23 :
      z180K30ProjectiveD6FallbackTargetTailV97B23.Perm z180K30ProjectiveD6FallbackTargetRemainderV97B23 := by
    change (z180K30ProjectiveD6FallbackTargetBucketV97B23 ++ z180K30ProjectiveD6FallbackTargetTailV97B24).Perm _
    exact
      ((List.Perm.refl z180K30ProjectiveD6FallbackTargetBucketV97B23).append hTarget24).trans
        hTargetSplit23
  have hBuckets23 :
      z180K30ProjectiveD6FallbackSourceTailV97B23.Perm z180K30ProjectiveD6FallbackTargetTailV97B23 := by
    change (z180K30ProjectiveD6FallbackSourceBucketV97B23 ++ z180K30ProjectiveD6FallbackSourceTailV97B24).Perm
      (z180K30ProjectiveD6FallbackTargetBucketV97B23 ++ z180K30ProjectiveD6FallbackTargetTailV97B24)
    exact
      z180_k30_projective_d6_fallback_bucket_v97_b23.append hBuckets24
  have hSourceSplit22 :
      (z180K30ProjectiveD6FallbackSourceBucketV97B22 ++ z180K30ProjectiveD6FallbackSourceRemainderV97B23).Perm
        z180K30ProjectiveD6FallbackSourceRemainderV97B22 := by
    simpa only [z180K30ProjectiveD6FallbackSourceBucketV97B22, z180K30ProjectiveD6FallbackSourceRemainderV97B23] using
      (List.filter_append_perm
        (z180K30ProjectiveD6FallbackPredicateV97 22)
        z180K30ProjectiveD6FallbackSourceRemainderV97B22)
  have hTargetSplit22 :
      (z180K30ProjectiveD6FallbackTargetBucketV97B22 ++ z180K30ProjectiveD6FallbackTargetRemainderV97B23).Perm
        z180K30ProjectiveD6FallbackTargetRemainderV97B22 := by
    simpa only [z180K30ProjectiveD6FallbackTargetBucketV97B22, z180K30ProjectiveD6FallbackTargetRemainderV97B23] using
      (List.filter_append_perm
        (z180K30ProjectiveD6FallbackPredicateV97 22)
        z180K30ProjectiveD6FallbackTargetRemainderV97B22)
  have hSource22 :
      z180K30ProjectiveD6FallbackSourceTailV97B22.Perm z180K30ProjectiveD6FallbackSourceRemainderV97B22 := by
    change (z180K30ProjectiveD6FallbackSourceBucketV97B22 ++ z180K30ProjectiveD6FallbackSourceTailV97B23).Perm _
    exact
      ((List.Perm.refl z180K30ProjectiveD6FallbackSourceBucketV97B22).append hSource23).trans
        hSourceSplit22
  have hTarget22 :
      z180K30ProjectiveD6FallbackTargetTailV97B22.Perm z180K30ProjectiveD6FallbackTargetRemainderV97B22 := by
    change (z180K30ProjectiveD6FallbackTargetBucketV97B22 ++ z180K30ProjectiveD6FallbackTargetTailV97B23).Perm _
    exact
      ((List.Perm.refl z180K30ProjectiveD6FallbackTargetBucketV97B22).append hTarget23).trans
        hTargetSplit22
  have hBuckets22 :
      z180K30ProjectiveD6FallbackSourceTailV97B22.Perm z180K30ProjectiveD6FallbackTargetTailV97B22 := by
    change (z180K30ProjectiveD6FallbackSourceBucketV97B22 ++ z180K30ProjectiveD6FallbackSourceTailV97B23).Perm
      (z180K30ProjectiveD6FallbackTargetBucketV97B22 ++ z180K30ProjectiveD6FallbackTargetTailV97B23)
    exact
      z180_k30_projective_d6_fallback_bucket_v97_b22.append hBuckets23
  have hSourceSplit21 :
      (z180K30ProjectiveD6FallbackSourceBucketV97B21 ++ z180K30ProjectiveD6FallbackSourceRemainderV97B22).Perm
        z180K30ProjectiveD6FallbackSourceRemainderV97B21 := by
    simpa only [z180K30ProjectiveD6FallbackSourceBucketV97B21, z180K30ProjectiveD6FallbackSourceRemainderV97B22] using
      (List.filter_append_perm
        (z180K30ProjectiveD6FallbackPredicateV97 21)
        z180K30ProjectiveD6FallbackSourceRemainderV97B21)
  have hTargetSplit21 :
      (z180K30ProjectiveD6FallbackTargetBucketV97B21 ++ z180K30ProjectiveD6FallbackTargetRemainderV97B22).Perm
        z180K30ProjectiveD6FallbackTargetRemainderV97B21 := by
    simpa only [z180K30ProjectiveD6FallbackTargetBucketV97B21, z180K30ProjectiveD6FallbackTargetRemainderV97B22] using
      (List.filter_append_perm
        (z180K30ProjectiveD6FallbackPredicateV97 21)
        z180K30ProjectiveD6FallbackTargetRemainderV97B21)
  have hSource21 :
      z180K30ProjectiveD6FallbackSourceTailV97B21.Perm z180K30ProjectiveD6FallbackSourceRemainderV97B21 := by
    change (z180K30ProjectiveD6FallbackSourceBucketV97B21 ++ z180K30ProjectiveD6FallbackSourceTailV97B22).Perm _
    exact
      ((List.Perm.refl z180K30ProjectiveD6FallbackSourceBucketV97B21).append hSource22).trans
        hSourceSplit21
  have hTarget21 :
      z180K30ProjectiveD6FallbackTargetTailV97B21.Perm z180K30ProjectiveD6FallbackTargetRemainderV97B21 := by
    change (z180K30ProjectiveD6FallbackTargetBucketV97B21 ++ z180K30ProjectiveD6FallbackTargetTailV97B22).Perm _
    exact
      ((List.Perm.refl z180K30ProjectiveD6FallbackTargetBucketV97B21).append hTarget22).trans
        hTargetSplit21
  have hBuckets21 :
      z180K30ProjectiveD6FallbackSourceTailV97B21.Perm z180K30ProjectiveD6FallbackTargetTailV97B21 := by
    change (z180K30ProjectiveD6FallbackSourceBucketV97B21 ++ z180K30ProjectiveD6FallbackSourceTailV97B22).Perm
      (z180K30ProjectiveD6FallbackTargetBucketV97B21 ++ z180K30ProjectiveD6FallbackTargetTailV97B22)
    exact
      z180_k30_projective_d6_fallback_bucket_v97_b21.append hBuckets22
  have hSourceSplit20 :
      (z180K30ProjectiveD6FallbackSourceBucketV97B20 ++ z180K30ProjectiveD6FallbackSourceRemainderV97B21).Perm
        z180K30ProjectiveD6FallbackSourceRemainderV97B20 := by
    simpa only [z180K30ProjectiveD6FallbackSourceBucketV97B20, z180K30ProjectiveD6FallbackSourceRemainderV97B21] using
      (List.filter_append_perm
        (z180K30ProjectiveD6FallbackPredicateV97 20)
        z180K30ProjectiveD6FallbackSourceRemainderV97B20)
  have hTargetSplit20 :
      (z180K30ProjectiveD6FallbackTargetBucketV97B20 ++ z180K30ProjectiveD6FallbackTargetRemainderV97B21).Perm
        z180K30ProjectiveD6FallbackTargetRemainderV97B20 := by
    simpa only [z180K30ProjectiveD6FallbackTargetBucketV97B20, z180K30ProjectiveD6FallbackTargetRemainderV97B21] using
      (List.filter_append_perm
        (z180K30ProjectiveD6FallbackPredicateV97 20)
        z180K30ProjectiveD6FallbackTargetRemainderV97B20)
  have hSource20 :
      z180K30ProjectiveD6FallbackSourceTailV97B20.Perm z180K30ProjectiveD6FallbackSourceRemainderV97B20 := by
    change (z180K30ProjectiveD6FallbackSourceBucketV97B20 ++ z180K30ProjectiveD6FallbackSourceTailV97B21).Perm _
    exact
      ((List.Perm.refl z180K30ProjectiveD6FallbackSourceBucketV97B20).append hSource21).trans
        hSourceSplit20
  have hTarget20 :
      z180K30ProjectiveD6FallbackTargetTailV97B20.Perm z180K30ProjectiveD6FallbackTargetRemainderV97B20 := by
    change (z180K30ProjectiveD6FallbackTargetBucketV97B20 ++ z180K30ProjectiveD6FallbackTargetTailV97B21).Perm _
    exact
      ((List.Perm.refl z180K30ProjectiveD6FallbackTargetBucketV97B20).append hTarget21).trans
        hTargetSplit20
  have hBuckets20 :
      z180K30ProjectiveD6FallbackSourceTailV97B20.Perm z180K30ProjectiveD6FallbackTargetTailV97B20 := by
    change (z180K30ProjectiveD6FallbackSourceBucketV97B20 ++ z180K30ProjectiveD6FallbackSourceTailV97B21).Perm
      (z180K30ProjectiveD6FallbackTargetBucketV97B20 ++ z180K30ProjectiveD6FallbackTargetTailV97B21)
    exact
      z180_k30_projective_d6_fallback_bucket_v97_b20.append hBuckets21
  have hSourceSplit19 :
      (z180K30ProjectiveD6FallbackSourceBucketV97B19 ++ z180K30ProjectiveD6FallbackSourceRemainderV97B20).Perm
        z180K30ProjectiveD6FallbackSourceRemainderV97B19 := by
    simpa only [z180K30ProjectiveD6FallbackSourceBucketV97B19, z180K30ProjectiveD6FallbackSourceRemainderV97B20] using
      (List.filter_append_perm
        (z180K30ProjectiveD6FallbackPredicateV97 19)
        z180K30ProjectiveD6FallbackSourceRemainderV97B19)
  have hTargetSplit19 :
      (z180K30ProjectiveD6FallbackTargetBucketV97B19 ++ z180K30ProjectiveD6FallbackTargetRemainderV97B20).Perm
        z180K30ProjectiveD6FallbackTargetRemainderV97B19 := by
    simpa only [z180K30ProjectiveD6FallbackTargetBucketV97B19, z180K30ProjectiveD6FallbackTargetRemainderV97B20] using
      (List.filter_append_perm
        (z180K30ProjectiveD6FallbackPredicateV97 19)
        z180K30ProjectiveD6FallbackTargetRemainderV97B19)
  have hSource19 :
      z180K30ProjectiveD6FallbackSourceTailV97B19.Perm z180K30ProjectiveD6FallbackSourceRemainderV97B19 := by
    change (z180K30ProjectiveD6FallbackSourceBucketV97B19 ++ z180K30ProjectiveD6FallbackSourceTailV97B20).Perm _
    exact
      ((List.Perm.refl z180K30ProjectiveD6FallbackSourceBucketV97B19).append hSource20).trans
        hSourceSplit19
  have hTarget19 :
      z180K30ProjectiveD6FallbackTargetTailV97B19.Perm z180K30ProjectiveD6FallbackTargetRemainderV97B19 := by
    change (z180K30ProjectiveD6FallbackTargetBucketV97B19 ++ z180K30ProjectiveD6FallbackTargetTailV97B20).Perm _
    exact
      ((List.Perm.refl z180K30ProjectiveD6FallbackTargetBucketV97B19).append hTarget20).trans
        hTargetSplit19
  have hBuckets19 :
      z180K30ProjectiveD6FallbackSourceTailV97B19.Perm z180K30ProjectiveD6FallbackTargetTailV97B19 := by
    change (z180K30ProjectiveD6FallbackSourceBucketV97B19 ++ z180K30ProjectiveD6FallbackSourceTailV97B20).Perm
      (z180K30ProjectiveD6FallbackTargetBucketV97B19 ++ z180K30ProjectiveD6FallbackTargetTailV97B20)
    exact
      z180_k30_projective_d6_fallback_bucket_v97_b19.append hBuckets20
  have hSourceSplit18 :
      (z180K30ProjectiveD6FallbackSourceBucketV97B18 ++ z180K30ProjectiveD6FallbackSourceRemainderV97B19).Perm
        z180K30ProjectiveD6FallbackSourceRemainderV97B18 := by
    simpa only [z180K30ProjectiveD6FallbackSourceBucketV97B18, z180K30ProjectiveD6FallbackSourceRemainderV97B19] using
      (List.filter_append_perm
        (z180K30ProjectiveD6FallbackPredicateV97 18)
        z180K30ProjectiveD6FallbackSourceRemainderV97B18)
  have hTargetSplit18 :
      (z180K30ProjectiveD6FallbackTargetBucketV97B18 ++ z180K30ProjectiveD6FallbackTargetRemainderV97B19).Perm
        z180K30ProjectiveD6FallbackTargetRemainderV97B18 := by
    simpa only [z180K30ProjectiveD6FallbackTargetBucketV97B18, z180K30ProjectiveD6FallbackTargetRemainderV97B19] using
      (List.filter_append_perm
        (z180K30ProjectiveD6FallbackPredicateV97 18)
        z180K30ProjectiveD6FallbackTargetRemainderV97B18)
  have hSource18 :
      z180K30ProjectiveD6FallbackSourceTailV97B18.Perm z180K30ProjectiveD6FallbackSourceRemainderV97B18 := by
    change (z180K30ProjectiveD6FallbackSourceBucketV97B18 ++ z180K30ProjectiveD6FallbackSourceTailV97B19).Perm _
    exact
      ((List.Perm.refl z180K30ProjectiveD6FallbackSourceBucketV97B18).append hSource19).trans
        hSourceSplit18
  have hTarget18 :
      z180K30ProjectiveD6FallbackTargetTailV97B18.Perm z180K30ProjectiveD6FallbackTargetRemainderV97B18 := by
    change (z180K30ProjectiveD6FallbackTargetBucketV97B18 ++ z180K30ProjectiveD6FallbackTargetTailV97B19).Perm _
    exact
      ((List.Perm.refl z180K30ProjectiveD6FallbackTargetBucketV97B18).append hTarget19).trans
        hTargetSplit18
  have hBuckets18 :
      z180K30ProjectiveD6FallbackSourceTailV97B18.Perm z180K30ProjectiveD6FallbackTargetTailV97B18 := by
    change (z180K30ProjectiveD6FallbackSourceBucketV97B18 ++ z180K30ProjectiveD6FallbackSourceTailV97B19).Perm
      (z180K30ProjectiveD6FallbackTargetBucketV97B18 ++ z180K30ProjectiveD6FallbackTargetTailV97B19)
    exact
      z180_k30_projective_d6_fallback_bucket_v97_b18.append hBuckets19
  have hSourceSplit17 :
      (z180K30ProjectiveD6FallbackSourceBucketV97B17 ++ z180K30ProjectiveD6FallbackSourceRemainderV97B18).Perm
        z180K30ProjectiveD6FallbackSourceRemainderV97B17 := by
    simpa only [z180K30ProjectiveD6FallbackSourceBucketV97B17, z180K30ProjectiveD6FallbackSourceRemainderV97B18] using
      (List.filter_append_perm
        (z180K30ProjectiveD6FallbackPredicateV97 17)
        z180K30ProjectiveD6FallbackSourceRemainderV97B17)
  have hTargetSplit17 :
      (z180K30ProjectiveD6FallbackTargetBucketV97B17 ++ z180K30ProjectiveD6FallbackTargetRemainderV97B18).Perm
        z180K30ProjectiveD6FallbackTargetRemainderV97B17 := by
    simpa only [z180K30ProjectiveD6FallbackTargetBucketV97B17, z180K30ProjectiveD6FallbackTargetRemainderV97B18] using
      (List.filter_append_perm
        (z180K30ProjectiveD6FallbackPredicateV97 17)
        z180K30ProjectiveD6FallbackTargetRemainderV97B17)
  have hSource17 :
      z180K30ProjectiveD6FallbackSourceTailV97B17.Perm z180K30ProjectiveD6FallbackSourceRemainderV97B17 := by
    change (z180K30ProjectiveD6FallbackSourceBucketV97B17 ++ z180K30ProjectiveD6FallbackSourceTailV97B18).Perm _
    exact
      ((List.Perm.refl z180K30ProjectiveD6FallbackSourceBucketV97B17).append hSource18).trans
        hSourceSplit17
  have hTarget17 :
      z180K30ProjectiveD6FallbackTargetTailV97B17.Perm z180K30ProjectiveD6FallbackTargetRemainderV97B17 := by
    change (z180K30ProjectiveD6FallbackTargetBucketV97B17 ++ z180K30ProjectiveD6FallbackTargetTailV97B18).Perm _
    exact
      ((List.Perm.refl z180K30ProjectiveD6FallbackTargetBucketV97B17).append hTarget18).trans
        hTargetSplit17
  have hBuckets17 :
      z180K30ProjectiveD6FallbackSourceTailV97B17.Perm z180K30ProjectiveD6FallbackTargetTailV97B17 := by
    change (z180K30ProjectiveD6FallbackSourceBucketV97B17 ++ z180K30ProjectiveD6FallbackSourceTailV97B18).Perm
      (z180K30ProjectiveD6FallbackTargetBucketV97B17 ++ z180K30ProjectiveD6FallbackTargetTailV97B18)
    exact
      z180_k30_projective_d6_fallback_bucket_v97_b17.append hBuckets18
  have hSourceSplit16 :
      (z180K30ProjectiveD6FallbackSourceBucketV97B16 ++ z180K30ProjectiveD6FallbackSourceRemainderV97B17).Perm
        z180K30ProjectiveD6FallbackSourceRemainderV97B16 := by
    simpa only [z180K30ProjectiveD6FallbackSourceBucketV97B16, z180K30ProjectiveD6FallbackSourceRemainderV97B17] using
      (List.filter_append_perm
        (z180K30ProjectiveD6FallbackPredicateV97 16)
        z180K30ProjectiveD6FallbackSourceRemainderV97B16)
  have hTargetSplit16 :
      (z180K30ProjectiveD6FallbackTargetBucketV97B16 ++ z180K30ProjectiveD6FallbackTargetRemainderV97B17).Perm
        z180K30ProjectiveD6FallbackTargetRemainderV97B16 := by
    simpa only [z180K30ProjectiveD6FallbackTargetBucketV97B16, z180K30ProjectiveD6FallbackTargetRemainderV97B17] using
      (List.filter_append_perm
        (z180K30ProjectiveD6FallbackPredicateV97 16)
        z180K30ProjectiveD6FallbackTargetRemainderV97B16)
  have hSource16 :
      z180K30ProjectiveD6FallbackSourceTailV97B16.Perm z180K30ProjectiveD6FallbackSourceRemainderV97B16 := by
    change (z180K30ProjectiveD6FallbackSourceBucketV97B16 ++ z180K30ProjectiveD6FallbackSourceTailV97B17).Perm _
    exact
      ((List.Perm.refl z180K30ProjectiveD6FallbackSourceBucketV97B16).append hSource17).trans
        hSourceSplit16
  have hTarget16 :
      z180K30ProjectiveD6FallbackTargetTailV97B16.Perm z180K30ProjectiveD6FallbackTargetRemainderV97B16 := by
    change (z180K30ProjectiveD6FallbackTargetBucketV97B16 ++ z180K30ProjectiveD6FallbackTargetTailV97B17).Perm _
    exact
      ((List.Perm.refl z180K30ProjectiveD6FallbackTargetBucketV97B16).append hTarget17).trans
        hTargetSplit16
  have hBuckets16 :
      z180K30ProjectiveD6FallbackSourceTailV97B16.Perm z180K30ProjectiveD6FallbackTargetTailV97B16 := by
    change (z180K30ProjectiveD6FallbackSourceBucketV97B16 ++ z180K30ProjectiveD6FallbackSourceTailV97B17).Perm
      (z180K30ProjectiveD6FallbackTargetBucketV97B16 ++ z180K30ProjectiveD6FallbackTargetTailV97B17)
    exact
      z180_k30_projective_d6_fallback_bucket_v97_b16.append hBuckets17
  have hSourceSplit15 :
      (z180K30ProjectiveD6FallbackSourceBucketV97B15 ++ z180K30ProjectiveD6FallbackSourceRemainderV97B16).Perm
        z180K30ProjectiveD6FallbackSourceRemainderV97B15 := by
    simpa only [z180K30ProjectiveD6FallbackSourceBucketV97B15, z180K30ProjectiveD6FallbackSourceRemainderV97B16] using
      (List.filter_append_perm
        (z180K30ProjectiveD6FallbackPredicateV97 15)
        z180K30ProjectiveD6FallbackSourceRemainderV97B15)
  have hTargetSplit15 :
      (z180K30ProjectiveD6FallbackTargetBucketV97B15 ++ z180K30ProjectiveD6FallbackTargetRemainderV97B16).Perm
        z180K30ProjectiveD6FallbackTargetRemainderV97B15 := by
    simpa only [z180K30ProjectiveD6FallbackTargetBucketV97B15, z180K30ProjectiveD6FallbackTargetRemainderV97B16] using
      (List.filter_append_perm
        (z180K30ProjectiveD6FallbackPredicateV97 15)
        z180K30ProjectiveD6FallbackTargetRemainderV97B15)
  have hSource15 :
      z180K30ProjectiveD6FallbackSourceTailV97B15.Perm z180K30ProjectiveD6FallbackSourceRemainderV97B15 := by
    change (z180K30ProjectiveD6FallbackSourceBucketV97B15 ++ z180K30ProjectiveD6FallbackSourceTailV97B16).Perm _
    exact
      ((List.Perm.refl z180K30ProjectiveD6FallbackSourceBucketV97B15).append hSource16).trans
        hSourceSplit15
  have hTarget15 :
      z180K30ProjectiveD6FallbackTargetTailV97B15.Perm z180K30ProjectiveD6FallbackTargetRemainderV97B15 := by
    change (z180K30ProjectiveD6FallbackTargetBucketV97B15 ++ z180K30ProjectiveD6FallbackTargetTailV97B16).Perm _
    exact
      ((List.Perm.refl z180K30ProjectiveD6FallbackTargetBucketV97B15).append hTarget16).trans
        hTargetSplit15
  have hBuckets15 :
      z180K30ProjectiveD6FallbackSourceTailV97B15.Perm z180K30ProjectiveD6FallbackTargetTailV97B15 := by
    change (z180K30ProjectiveD6FallbackSourceBucketV97B15 ++ z180K30ProjectiveD6FallbackSourceTailV97B16).Perm
      (z180K30ProjectiveD6FallbackTargetBucketV97B15 ++ z180K30ProjectiveD6FallbackTargetTailV97B16)
    exact
      z180_k30_projective_d6_fallback_bucket_v97_b15.append hBuckets16
  have hSourceSplit14 :
      (z180K30ProjectiveD6FallbackSourceBucketV97B14 ++ z180K30ProjectiveD6FallbackSourceRemainderV97B15).Perm
        z180K30ProjectiveD6FallbackSourceRemainderV97B14 := by
    simpa only [z180K30ProjectiveD6FallbackSourceBucketV97B14, z180K30ProjectiveD6FallbackSourceRemainderV97B15] using
      (List.filter_append_perm
        (z180K30ProjectiveD6FallbackPredicateV97 14)
        z180K30ProjectiveD6FallbackSourceRemainderV97B14)
  have hTargetSplit14 :
      (z180K30ProjectiveD6FallbackTargetBucketV97B14 ++ z180K30ProjectiveD6FallbackTargetRemainderV97B15).Perm
        z180K30ProjectiveD6FallbackTargetRemainderV97B14 := by
    simpa only [z180K30ProjectiveD6FallbackTargetBucketV97B14, z180K30ProjectiveD6FallbackTargetRemainderV97B15] using
      (List.filter_append_perm
        (z180K30ProjectiveD6FallbackPredicateV97 14)
        z180K30ProjectiveD6FallbackTargetRemainderV97B14)
  have hSource14 :
      z180K30ProjectiveD6FallbackSourceTailV97B14.Perm z180K30ProjectiveD6FallbackSourceRemainderV97B14 := by
    change (z180K30ProjectiveD6FallbackSourceBucketV97B14 ++ z180K30ProjectiveD6FallbackSourceTailV97B15).Perm _
    exact
      ((List.Perm.refl z180K30ProjectiveD6FallbackSourceBucketV97B14).append hSource15).trans
        hSourceSplit14
  have hTarget14 :
      z180K30ProjectiveD6FallbackTargetTailV97B14.Perm z180K30ProjectiveD6FallbackTargetRemainderV97B14 := by
    change (z180K30ProjectiveD6FallbackTargetBucketV97B14 ++ z180K30ProjectiveD6FallbackTargetTailV97B15).Perm _
    exact
      ((List.Perm.refl z180K30ProjectiveD6FallbackTargetBucketV97B14).append hTarget15).trans
        hTargetSplit14
  have hBuckets14 :
      z180K30ProjectiveD6FallbackSourceTailV97B14.Perm z180K30ProjectiveD6FallbackTargetTailV97B14 := by
    change (z180K30ProjectiveD6FallbackSourceBucketV97B14 ++ z180K30ProjectiveD6FallbackSourceTailV97B15).Perm
      (z180K30ProjectiveD6FallbackTargetBucketV97B14 ++ z180K30ProjectiveD6FallbackTargetTailV97B15)
    exact
      z180_k30_projective_d6_fallback_bucket_v97_b14.append hBuckets15
  have hSourceSplit13 :
      (z180K30ProjectiveD6FallbackSourceBucketV97B13 ++ z180K30ProjectiveD6FallbackSourceRemainderV97B14).Perm
        z180K30ProjectiveD6FallbackSourceRemainderV97B13 := by
    simpa only [z180K30ProjectiveD6FallbackSourceBucketV97B13, z180K30ProjectiveD6FallbackSourceRemainderV97B14] using
      (List.filter_append_perm
        (z180K30ProjectiveD6FallbackPredicateV97 13)
        z180K30ProjectiveD6FallbackSourceRemainderV97B13)
  have hTargetSplit13 :
      (z180K30ProjectiveD6FallbackTargetBucketV97B13 ++ z180K30ProjectiveD6FallbackTargetRemainderV97B14).Perm
        z180K30ProjectiveD6FallbackTargetRemainderV97B13 := by
    simpa only [z180K30ProjectiveD6FallbackTargetBucketV97B13, z180K30ProjectiveD6FallbackTargetRemainderV97B14] using
      (List.filter_append_perm
        (z180K30ProjectiveD6FallbackPredicateV97 13)
        z180K30ProjectiveD6FallbackTargetRemainderV97B13)
  have hSource13 :
      z180K30ProjectiveD6FallbackSourceTailV97B13.Perm z180K30ProjectiveD6FallbackSourceRemainderV97B13 := by
    change (z180K30ProjectiveD6FallbackSourceBucketV97B13 ++ z180K30ProjectiveD6FallbackSourceTailV97B14).Perm _
    exact
      ((List.Perm.refl z180K30ProjectiveD6FallbackSourceBucketV97B13).append hSource14).trans
        hSourceSplit13
  have hTarget13 :
      z180K30ProjectiveD6FallbackTargetTailV97B13.Perm z180K30ProjectiveD6FallbackTargetRemainderV97B13 := by
    change (z180K30ProjectiveD6FallbackTargetBucketV97B13 ++ z180K30ProjectiveD6FallbackTargetTailV97B14).Perm _
    exact
      ((List.Perm.refl z180K30ProjectiveD6FallbackTargetBucketV97B13).append hTarget14).trans
        hTargetSplit13
  have hBuckets13 :
      z180K30ProjectiveD6FallbackSourceTailV97B13.Perm z180K30ProjectiveD6FallbackTargetTailV97B13 := by
    change (z180K30ProjectiveD6FallbackSourceBucketV97B13 ++ z180K30ProjectiveD6FallbackSourceTailV97B14).Perm
      (z180K30ProjectiveD6FallbackTargetBucketV97B13 ++ z180K30ProjectiveD6FallbackTargetTailV97B14)
    exact
      z180_k30_projective_d6_fallback_bucket_v97_b13.append hBuckets14
  have hSourceSplit12 :
      (z180K30ProjectiveD6FallbackSourceBucketV97B12 ++ z180K30ProjectiveD6FallbackSourceRemainderV97B13).Perm
        z180K30ProjectiveD6FallbackSourceRemainderV97B12 := by
    simpa only [z180K30ProjectiveD6FallbackSourceBucketV97B12, z180K30ProjectiveD6FallbackSourceRemainderV97B13] using
      (List.filter_append_perm
        (z180K30ProjectiveD6FallbackPredicateV97 12)
        z180K30ProjectiveD6FallbackSourceRemainderV97B12)
  have hTargetSplit12 :
      (z180K30ProjectiveD6FallbackTargetBucketV97B12 ++ z180K30ProjectiveD6FallbackTargetRemainderV97B13).Perm
        z180K30ProjectiveD6FallbackTargetRemainderV97B12 := by
    simpa only [z180K30ProjectiveD6FallbackTargetBucketV97B12, z180K30ProjectiveD6FallbackTargetRemainderV97B13] using
      (List.filter_append_perm
        (z180K30ProjectiveD6FallbackPredicateV97 12)
        z180K30ProjectiveD6FallbackTargetRemainderV97B12)
  have hSource12 :
      z180K30ProjectiveD6FallbackSourceTailV97B12.Perm z180K30ProjectiveD6FallbackSourceRemainderV97B12 := by
    change (z180K30ProjectiveD6FallbackSourceBucketV97B12 ++ z180K30ProjectiveD6FallbackSourceTailV97B13).Perm _
    exact
      ((List.Perm.refl z180K30ProjectiveD6FallbackSourceBucketV97B12).append hSource13).trans
        hSourceSplit12
  have hTarget12 :
      z180K30ProjectiveD6FallbackTargetTailV97B12.Perm z180K30ProjectiveD6FallbackTargetRemainderV97B12 := by
    change (z180K30ProjectiveD6FallbackTargetBucketV97B12 ++ z180K30ProjectiveD6FallbackTargetTailV97B13).Perm _
    exact
      ((List.Perm.refl z180K30ProjectiveD6FallbackTargetBucketV97B12).append hTarget13).trans
        hTargetSplit12
  have hBuckets12 :
      z180K30ProjectiveD6FallbackSourceTailV97B12.Perm z180K30ProjectiveD6FallbackTargetTailV97B12 := by
    change (z180K30ProjectiveD6FallbackSourceBucketV97B12 ++ z180K30ProjectiveD6FallbackSourceTailV97B13).Perm
      (z180K30ProjectiveD6FallbackTargetBucketV97B12 ++ z180K30ProjectiveD6FallbackTargetTailV97B13)
    exact
      z180_k30_projective_d6_fallback_bucket_v97_b12.append hBuckets13
  have hSourceSplit11 :
      (z180K30ProjectiveD6FallbackSourceBucketV97B11 ++ z180K30ProjectiveD6FallbackSourceRemainderV97B12).Perm
        z180K30ProjectiveD6FallbackSourceRemainderV97B11 := by
    simpa only [z180K30ProjectiveD6FallbackSourceBucketV97B11, z180K30ProjectiveD6FallbackSourceRemainderV97B12] using
      (List.filter_append_perm
        (z180K30ProjectiveD6FallbackPredicateV97 11)
        z180K30ProjectiveD6FallbackSourceRemainderV97B11)
  have hTargetSplit11 :
      (z180K30ProjectiveD6FallbackTargetBucketV97B11 ++ z180K30ProjectiveD6FallbackTargetRemainderV97B12).Perm
        z180K30ProjectiveD6FallbackTargetRemainderV97B11 := by
    simpa only [z180K30ProjectiveD6FallbackTargetBucketV97B11, z180K30ProjectiveD6FallbackTargetRemainderV97B12] using
      (List.filter_append_perm
        (z180K30ProjectiveD6FallbackPredicateV97 11)
        z180K30ProjectiveD6FallbackTargetRemainderV97B11)
  have hSource11 :
      z180K30ProjectiveD6FallbackSourceTailV97B11.Perm z180K30ProjectiveD6FallbackSourceRemainderV97B11 := by
    change (z180K30ProjectiveD6FallbackSourceBucketV97B11 ++ z180K30ProjectiveD6FallbackSourceTailV97B12).Perm _
    exact
      ((List.Perm.refl z180K30ProjectiveD6FallbackSourceBucketV97B11).append hSource12).trans
        hSourceSplit11
  have hTarget11 :
      z180K30ProjectiveD6FallbackTargetTailV97B11.Perm z180K30ProjectiveD6FallbackTargetRemainderV97B11 := by
    change (z180K30ProjectiveD6FallbackTargetBucketV97B11 ++ z180K30ProjectiveD6FallbackTargetTailV97B12).Perm _
    exact
      ((List.Perm.refl z180K30ProjectiveD6FallbackTargetBucketV97B11).append hTarget12).trans
        hTargetSplit11
  have hBuckets11 :
      z180K30ProjectiveD6FallbackSourceTailV97B11.Perm z180K30ProjectiveD6FallbackTargetTailV97B11 := by
    change (z180K30ProjectiveD6FallbackSourceBucketV97B11 ++ z180K30ProjectiveD6FallbackSourceTailV97B12).Perm
      (z180K30ProjectiveD6FallbackTargetBucketV97B11 ++ z180K30ProjectiveD6FallbackTargetTailV97B12)
    exact
      z180_k30_projective_d6_fallback_bucket_v97_b11.append hBuckets12
  have hSourceSplit10 :
      (z180K30ProjectiveD6FallbackSourceBucketV97B10 ++ z180K30ProjectiveD6FallbackSourceRemainderV97B11).Perm
        z180K30ProjectiveD6FallbackSourceRemainderV97B10 := by
    simpa only [z180K30ProjectiveD6FallbackSourceBucketV97B10, z180K30ProjectiveD6FallbackSourceRemainderV97B11] using
      (List.filter_append_perm
        (z180K30ProjectiveD6FallbackPredicateV97 10)
        z180K30ProjectiveD6FallbackSourceRemainderV97B10)
  have hTargetSplit10 :
      (z180K30ProjectiveD6FallbackTargetBucketV97B10 ++ z180K30ProjectiveD6FallbackTargetRemainderV97B11).Perm
        z180K30ProjectiveD6FallbackTargetRemainderV97B10 := by
    simpa only [z180K30ProjectiveD6FallbackTargetBucketV97B10, z180K30ProjectiveD6FallbackTargetRemainderV97B11] using
      (List.filter_append_perm
        (z180K30ProjectiveD6FallbackPredicateV97 10)
        z180K30ProjectiveD6FallbackTargetRemainderV97B10)
  have hSource10 :
      z180K30ProjectiveD6FallbackSourceTailV97B10.Perm z180K30ProjectiveD6FallbackSourceRemainderV97B10 := by
    change (z180K30ProjectiveD6FallbackSourceBucketV97B10 ++ z180K30ProjectiveD6FallbackSourceTailV97B11).Perm _
    exact
      ((List.Perm.refl z180K30ProjectiveD6FallbackSourceBucketV97B10).append hSource11).trans
        hSourceSplit10
  have hTarget10 :
      z180K30ProjectiveD6FallbackTargetTailV97B10.Perm z180K30ProjectiveD6FallbackTargetRemainderV97B10 := by
    change (z180K30ProjectiveD6FallbackTargetBucketV97B10 ++ z180K30ProjectiveD6FallbackTargetTailV97B11).Perm _
    exact
      ((List.Perm.refl z180K30ProjectiveD6FallbackTargetBucketV97B10).append hTarget11).trans
        hTargetSplit10
  have hBuckets10 :
      z180K30ProjectiveD6FallbackSourceTailV97B10.Perm z180K30ProjectiveD6FallbackTargetTailV97B10 := by
    change (z180K30ProjectiveD6FallbackSourceBucketV97B10 ++ z180K30ProjectiveD6FallbackSourceTailV97B11).Perm
      (z180K30ProjectiveD6FallbackTargetBucketV97B10 ++ z180K30ProjectiveD6FallbackTargetTailV97B11)
    exact
      z180_k30_projective_d6_fallback_bucket_v97_b10.append hBuckets11
  have hSourceSplit09 :
      (z180K30ProjectiveD6FallbackSourceBucketV97B09 ++ z180K30ProjectiveD6FallbackSourceRemainderV97B10).Perm
        z180K30ProjectiveD6FallbackSourceRemainderV97B09 := by
    simpa only [z180K30ProjectiveD6FallbackSourceBucketV97B09, z180K30ProjectiveD6FallbackSourceRemainderV97B10] using
      (List.filter_append_perm
        (z180K30ProjectiveD6FallbackPredicateV97 9)
        z180K30ProjectiveD6FallbackSourceRemainderV97B09)
  have hTargetSplit09 :
      (z180K30ProjectiveD6FallbackTargetBucketV97B09 ++ z180K30ProjectiveD6FallbackTargetRemainderV97B10).Perm
        z180K30ProjectiveD6FallbackTargetRemainderV97B09 := by
    simpa only [z180K30ProjectiveD6FallbackTargetBucketV97B09, z180K30ProjectiveD6FallbackTargetRemainderV97B10] using
      (List.filter_append_perm
        (z180K30ProjectiveD6FallbackPredicateV97 9)
        z180K30ProjectiveD6FallbackTargetRemainderV97B09)
  have hSource09 :
      z180K30ProjectiveD6FallbackSourceTailV97B09.Perm z180K30ProjectiveD6FallbackSourceRemainderV97B09 := by
    change (z180K30ProjectiveD6FallbackSourceBucketV97B09 ++ z180K30ProjectiveD6FallbackSourceTailV97B10).Perm _
    exact
      ((List.Perm.refl z180K30ProjectiveD6FallbackSourceBucketV97B09).append hSource10).trans
        hSourceSplit09
  have hTarget09 :
      z180K30ProjectiveD6FallbackTargetTailV97B09.Perm z180K30ProjectiveD6FallbackTargetRemainderV97B09 := by
    change (z180K30ProjectiveD6FallbackTargetBucketV97B09 ++ z180K30ProjectiveD6FallbackTargetTailV97B10).Perm _
    exact
      ((List.Perm.refl z180K30ProjectiveD6FallbackTargetBucketV97B09).append hTarget10).trans
        hTargetSplit09
  have hBuckets09 :
      z180K30ProjectiveD6FallbackSourceTailV97B09.Perm z180K30ProjectiveD6FallbackTargetTailV97B09 := by
    change (z180K30ProjectiveD6FallbackSourceBucketV97B09 ++ z180K30ProjectiveD6FallbackSourceTailV97B10).Perm
      (z180K30ProjectiveD6FallbackTargetBucketV97B09 ++ z180K30ProjectiveD6FallbackTargetTailV97B10)
    exact
      z180_k30_projective_d6_fallback_bucket_v97_b09.append hBuckets10
  have hSourceSplit08 :
      (z180K30ProjectiveD6FallbackSourceBucketV97B08 ++ z180K30ProjectiveD6FallbackSourceRemainderV97B09).Perm
        z180K30ProjectiveD6FallbackSourceRemainderV97B08 := by
    simpa only [z180K30ProjectiveD6FallbackSourceBucketV97B08, z180K30ProjectiveD6FallbackSourceRemainderV97B09] using
      (List.filter_append_perm
        (z180K30ProjectiveD6FallbackPredicateV97 8)
        z180K30ProjectiveD6FallbackSourceRemainderV97B08)
  have hTargetSplit08 :
      (z180K30ProjectiveD6FallbackTargetBucketV97B08 ++ z180K30ProjectiveD6FallbackTargetRemainderV97B09).Perm
        z180K30ProjectiveD6FallbackTargetRemainderV97B08 := by
    simpa only [z180K30ProjectiveD6FallbackTargetBucketV97B08, z180K30ProjectiveD6FallbackTargetRemainderV97B09] using
      (List.filter_append_perm
        (z180K30ProjectiveD6FallbackPredicateV97 8)
        z180K30ProjectiveD6FallbackTargetRemainderV97B08)
  have hSource08 :
      z180K30ProjectiveD6FallbackSourceTailV97B08.Perm z180K30ProjectiveD6FallbackSourceRemainderV97B08 := by
    change (z180K30ProjectiveD6FallbackSourceBucketV97B08 ++ z180K30ProjectiveD6FallbackSourceTailV97B09).Perm _
    exact
      ((List.Perm.refl z180K30ProjectiveD6FallbackSourceBucketV97B08).append hSource09).trans
        hSourceSplit08
  have hTarget08 :
      z180K30ProjectiveD6FallbackTargetTailV97B08.Perm z180K30ProjectiveD6FallbackTargetRemainderV97B08 := by
    change (z180K30ProjectiveD6FallbackTargetBucketV97B08 ++ z180K30ProjectiveD6FallbackTargetTailV97B09).Perm _
    exact
      ((List.Perm.refl z180K30ProjectiveD6FallbackTargetBucketV97B08).append hTarget09).trans
        hTargetSplit08
  have hBuckets08 :
      z180K30ProjectiveD6FallbackSourceTailV97B08.Perm z180K30ProjectiveD6FallbackTargetTailV97B08 := by
    change (z180K30ProjectiveD6FallbackSourceBucketV97B08 ++ z180K30ProjectiveD6FallbackSourceTailV97B09).Perm
      (z180K30ProjectiveD6FallbackTargetBucketV97B08 ++ z180K30ProjectiveD6FallbackTargetTailV97B09)
    exact
      z180_k30_projective_d6_fallback_bucket_v97_b08.append hBuckets09
  have hSourceSplit07 :
      (z180K30ProjectiveD6FallbackSourceBucketV97B07 ++ z180K30ProjectiveD6FallbackSourceRemainderV97B08).Perm
        z180K30ProjectiveD6FallbackSourceRemainderV97B07 := by
    simpa only [z180K30ProjectiveD6FallbackSourceBucketV97B07, z180K30ProjectiveD6FallbackSourceRemainderV97B08] using
      (List.filter_append_perm
        (z180K30ProjectiveD6FallbackPredicateV97 7)
        z180K30ProjectiveD6FallbackSourceRemainderV97B07)
  have hTargetSplit07 :
      (z180K30ProjectiveD6FallbackTargetBucketV97B07 ++ z180K30ProjectiveD6FallbackTargetRemainderV97B08).Perm
        z180K30ProjectiveD6FallbackTargetRemainderV97B07 := by
    simpa only [z180K30ProjectiveD6FallbackTargetBucketV97B07, z180K30ProjectiveD6FallbackTargetRemainderV97B08] using
      (List.filter_append_perm
        (z180K30ProjectiveD6FallbackPredicateV97 7)
        z180K30ProjectiveD6FallbackTargetRemainderV97B07)
  have hSource07 :
      z180K30ProjectiveD6FallbackSourceTailV97B07.Perm z180K30ProjectiveD6FallbackSourceRemainderV97B07 := by
    change (z180K30ProjectiveD6FallbackSourceBucketV97B07 ++ z180K30ProjectiveD6FallbackSourceTailV97B08).Perm _
    exact
      ((List.Perm.refl z180K30ProjectiveD6FallbackSourceBucketV97B07).append hSource08).trans
        hSourceSplit07
  have hTarget07 :
      z180K30ProjectiveD6FallbackTargetTailV97B07.Perm z180K30ProjectiveD6FallbackTargetRemainderV97B07 := by
    change (z180K30ProjectiveD6FallbackTargetBucketV97B07 ++ z180K30ProjectiveD6FallbackTargetTailV97B08).Perm _
    exact
      ((List.Perm.refl z180K30ProjectiveD6FallbackTargetBucketV97B07).append hTarget08).trans
        hTargetSplit07
  have hBuckets07 :
      z180K30ProjectiveD6FallbackSourceTailV97B07.Perm z180K30ProjectiveD6FallbackTargetTailV97B07 := by
    change (z180K30ProjectiveD6FallbackSourceBucketV97B07 ++ z180K30ProjectiveD6FallbackSourceTailV97B08).Perm
      (z180K30ProjectiveD6FallbackTargetBucketV97B07 ++ z180K30ProjectiveD6FallbackTargetTailV97B08)
    exact
      z180_k30_projective_d6_fallback_bucket_v97_b07.append hBuckets08
  have hSourceSplit06 :
      (z180K30ProjectiveD6FallbackSourceBucketV97B06 ++ z180K30ProjectiveD6FallbackSourceRemainderV97B07).Perm
        z180K30ProjectiveD6FallbackSourceRemainderV97B06 := by
    simpa only [z180K30ProjectiveD6FallbackSourceBucketV97B06, z180K30ProjectiveD6FallbackSourceRemainderV97B07] using
      (List.filter_append_perm
        (z180K30ProjectiveD6FallbackPredicateV97 6)
        z180K30ProjectiveD6FallbackSourceRemainderV97B06)
  have hTargetSplit06 :
      (z180K30ProjectiveD6FallbackTargetBucketV97B06 ++ z180K30ProjectiveD6FallbackTargetRemainderV97B07).Perm
        z180K30ProjectiveD6FallbackTargetRemainderV97B06 := by
    simpa only [z180K30ProjectiveD6FallbackTargetBucketV97B06, z180K30ProjectiveD6FallbackTargetRemainderV97B07] using
      (List.filter_append_perm
        (z180K30ProjectiveD6FallbackPredicateV97 6)
        z180K30ProjectiveD6FallbackTargetRemainderV97B06)
  have hSource06 :
      z180K30ProjectiveD6FallbackSourceTailV97B06.Perm z180K30ProjectiveD6FallbackSourceRemainderV97B06 := by
    change (z180K30ProjectiveD6FallbackSourceBucketV97B06 ++ z180K30ProjectiveD6FallbackSourceTailV97B07).Perm _
    exact
      ((List.Perm.refl z180K30ProjectiveD6FallbackSourceBucketV97B06).append hSource07).trans
        hSourceSplit06
  have hTarget06 :
      z180K30ProjectiveD6FallbackTargetTailV97B06.Perm z180K30ProjectiveD6FallbackTargetRemainderV97B06 := by
    change (z180K30ProjectiveD6FallbackTargetBucketV97B06 ++ z180K30ProjectiveD6FallbackTargetTailV97B07).Perm _
    exact
      ((List.Perm.refl z180K30ProjectiveD6FallbackTargetBucketV97B06).append hTarget07).trans
        hTargetSplit06
  have hBuckets06 :
      z180K30ProjectiveD6FallbackSourceTailV97B06.Perm z180K30ProjectiveD6FallbackTargetTailV97B06 := by
    change (z180K30ProjectiveD6FallbackSourceBucketV97B06 ++ z180K30ProjectiveD6FallbackSourceTailV97B07).Perm
      (z180K30ProjectiveD6FallbackTargetBucketV97B06 ++ z180K30ProjectiveD6FallbackTargetTailV97B07)
    exact
      z180_k30_projective_d6_fallback_bucket_v97_b06.append hBuckets07
  have hSourceSplit05 :
      (z180K30ProjectiveD6FallbackSourceBucketV97B05 ++ z180K30ProjectiveD6FallbackSourceRemainderV97B06).Perm
        z180K30ProjectiveD6FallbackSourceRemainderV97B05 := by
    simpa only [z180K30ProjectiveD6FallbackSourceBucketV97B05, z180K30ProjectiveD6FallbackSourceRemainderV97B06] using
      (List.filter_append_perm
        (z180K30ProjectiveD6FallbackPredicateV97 5)
        z180K30ProjectiveD6FallbackSourceRemainderV97B05)
  have hTargetSplit05 :
      (z180K30ProjectiveD6FallbackTargetBucketV97B05 ++ z180K30ProjectiveD6FallbackTargetRemainderV97B06).Perm
        z180K30ProjectiveD6FallbackTargetRemainderV97B05 := by
    simpa only [z180K30ProjectiveD6FallbackTargetBucketV97B05, z180K30ProjectiveD6FallbackTargetRemainderV97B06] using
      (List.filter_append_perm
        (z180K30ProjectiveD6FallbackPredicateV97 5)
        z180K30ProjectiveD6FallbackTargetRemainderV97B05)
  have hSource05 :
      z180K30ProjectiveD6FallbackSourceTailV97B05.Perm z180K30ProjectiveD6FallbackSourceRemainderV97B05 := by
    change (z180K30ProjectiveD6FallbackSourceBucketV97B05 ++ z180K30ProjectiveD6FallbackSourceTailV97B06).Perm _
    exact
      ((List.Perm.refl z180K30ProjectiveD6FallbackSourceBucketV97B05).append hSource06).trans
        hSourceSplit05
  have hTarget05 :
      z180K30ProjectiveD6FallbackTargetTailV97B05.Perm z180K30ProjectiveD6FallbackTargetRemainderV97B05 := by
    change (z180K30ProjectiveD6FallbackTargetBucketV97B05 ++ z180K30ProjectiveD6FallbackTargetTailV97B06).Perm _
    exact
      ((List.Perm.refl z180K30ProjectiveD6FallbackTargetBucketV97B05).append hTarget06).trans
        hTargetSplit05
  have hBuckets05 :
      z180K30ProjectiveD6FallbackSourceTailV97B05.Perm z180K30ProjectiveD6FallbackTargetTailV97B05 := by
    change (z180K30ProjectiveD6FallbackSourceBucketV97B05 ++ z180K30ProjectiveD6FallbackSourceTailV97B06).Perm
      (z180K30ProjectiveD6FallbackTargetBucketV97B05 ++ z180K30ProjectiveD6FallbackTargetTailV97B06)
    exact
      z180_k30_projective_d6_fallback_bucket_v97_b05.append hBuckets06
  have hSourceSplit04 :
      (z180K30ProjectiveD6FallbackSourceBucketV97B04 ++ z180K30ProjectiveD6FallbackSourceRemainderV97B05).Perm
        z180K30ProjectiveD6FallbackSourceRemainderV97B04 := by
    simpa only [z180K30ProjectiveD6FallbackSourceBucketV97B04, z180K30ProjectiveD6FallbackSourceRemainderV97B05] using
      (List.filter_append_perm
        (z180K30ProjectiveD6FallbackPredicateV97 4)
        z180K30ProjectiveD6FallbackSourceRemainderV97B04)
  have hTargetSplit04 :
      (z180K30ProjectiveD6FallbackTargetBucketV97B04 ++ z180K30ProjectiveD6FallbackTargetRemainderV97B05).Perm
        z180K30ProjectiveD6FallbackTargetRemainderV97B04 := by
    simpa only [z180K30ProjectiveD6FallbackTargetBucketV97B04, z180K30ProjectiveD6FallbackTargetRemainderV97B05] using
      (List.filter_append_perm
        (z180K30ProjectiveD6FallbackPredicateV97 4)
        z180K30ProjectiveD6FallbackTargetRemainderV97B04)
  have hSource04 :
      z180K30ProjectiveD6FallbackSourceTailV97B04.Perm z180K30ProjectiveD6FallbackSourceRemainderV97B04 := by
    change (z180K30ProjectiveD6FallbackSourceBucketV97B04 ++ z180K30ProjectiveD6FallbackSourceTailV97B05).Perm _
    exact
      ((List.Perm.refl z180K30ProjectiveD6FallbackSourceBucketV97B04).append hSource05).trans
        hSourceSplit04
  have hTarget04 :
      z180K30ProjectiveD6FallbackTargetTailV97B04.Perm z180K30ProjectiveD6FallbackTargetRemainderV97B04 := by
    change (z180K30ProjectiveD6FallbackTargetBucketV97B04 ++ z180K30ProjectiveD6FallbackTargetTailV97B05).Perm _
    exact
      ((List.Perm.refl z180K30ProjectiveD6FallbackTargetBucketV97B04).append hTarget05).trans
        hTargetSplit04
  have hBuckets04 :
      z180K30ProjectiveD6FallbackSourceTailV97B04.Perm z180K30ProjectiveD6FallbackTargetTailV97B04 := by
    change (z180K30ProjectiveD6FallbackSourceBucketV97B04 ++ z180K30ProjectiveD6FallbackSourceTailV97B05).Perm
      (z180K30ProjectiveD6FallbackTargetBucketV97B04 ++ z180K30ProjectiveD6FallbackTargetTailV97B05)
    exact
      z180_k30_projective_d6_fallback_bucket_v97_b04.append hBuckets05
  have hSourceSplit03 :
      (z180K30ProjectiveD6FallbackSourceBucketV97B03 ++ z180K30ProjectiveD6FallbackSourceRemainderV97B04).Perm
        z180K30ProjectiveD6FallbackSourceRemainderV97B03 := by
    simpa only [z180K30ProjectiveD6FallbackSourceBucketV97B03, z180K30ProjectiveD6FallbackSourceRemainderV97B04] using
      (List.filter_append_perm
        (z180K30ProjectiveD6FallbackPredicateV97 3)
        z180K30ProjectiveD6FallbackSourceRemainderV97B03)
  have hTargetSplit03 :
      (z180K30ProjectiveD6FallbackTargetBucketV97B03 ++ z180K30ProjectiveD6FallbackTargetRemainderV97B04).Perm
        z180K30ProjectiveD6FallbackTargetRemainderV97B03 := by
    simpa only [z180K30ProjectiveD6FallbackTargetBucketV97B03, z180K30ProjectiveD6FallbackTargetRemainderV97B04] using
      (List.filter_append_perm
        (z180K30ProjectiveD6FallbackPredicateV97 3)
        z180K30ProjectiveD6FallbackTargetRemainderV97B03)
  have hSource03 :
      z180K30ProjectiveD6FallbackSourceTailV97B03.Perm z180K30ProjectiveD6FallbackSourceRemainderV97B03 := by
    change (z180K30ProjectiveD6FallbackSourceBucketV97B03 ++ z180K30ProjectiveD6FallbackSourceTailV97B04).Perm _
    exact
      ((List.Perm.refl z180K30ProjectiveD6FallbackSourceBucketV97B03).append hSource04).trans
        hSourceSplit03
  have hTarget03 :
      z180K30ProjectiveD6FallbackTargetTailV97B03.Perm z180K30ProjectiveD6FallbackTargetRemainderV97B03 := by
    change (z180K30ProjectiveD6FallbackTargetBucketV97B03 ++ z180K30ProjectiveD6FallbackTargetTailV97B04).Perm _
    exact
      ((List.Perm.refl z180K30ProjectiveD6FallbackTargetBucketV97B03).append hTarget04).trans
        hTargetSplit03
  have hBuckets03 :
      z180K30ProjectiveD6FallbackSourceTailV97B03.Perm z180K30ProjectiveD6FallbackTargetTailV97B03 := by
    change (z180K30ProjectiveD6FallbackSourceBucketV97B03 ++ z180K30ProjectiveD6FallbackSourceTailV97B04).Perm
      (z180K30ProjectiveD6FallbackTargetBucketV97B03 ++ z180K30ProjectiveD6FallbackTargetTailV97B04)
    exact
      z180_k30_projective_d6_fallback_bucket_v97_b03.append hBuckets04
  have hSourceSplit02 :
      (z180K30ProjectiveD6FallbackSourceBucketV97B02 ++ z180K30ProjectiveD6FallbackSourceRemainderV97B03).Perm
        z180K30ProjectiveD6FallbackSourceRemainderV97B02 := by
    simpa only [z180K30ProjectiveD6FallbackSourceBucketV97B02, z180K30ProjectiveD6FallbackSourceRemainderV97B03] using
      (List.filter_append_perm
        (z180K30ProjectiveD6FallbackPredicateV97 2)
        z180K30ProjectiveD6FallbackSourceRemainderV97B02)
  have hTargetSplit02 :
      (z180K30ProjectiveD6FallbackTargetBucketV97B02 ++ z180K30ProjectiveD6FallbackTargetRemainderV97B03).Perm
        z180K30ProjectiveD6FallbackTargetRemainderV97B02 := by
    simpa only [z180K30ProjectiveD6FallbackTargetBucketV97B02, z180K30ProjectiveD6FallbackTargetRemainderV97B03] using
      (List.filter_append_perm
        (z180K30ProjectiveD6FallbackPredicateV97 2)
        z180K30ProjectiveD6FallbackTargetRemainderV97B02)
  have hSource02 :
      z180K30ProjectiveD6FallbackSourceTailV97B02.Perm z180K30ProjectiveD6FallbackSourceRemainderV97B02 := by
    change (z180K30ProjectiveD6FallbackSourceBucketV97B02 ++ z180K30ProjectiveD6FallbackSourceTailV97B03).Perm _
    exact
      ((List.Perm.refl z180K30ProjectiveD6FallbackSourceBucketV97B02).append hSource03).trans
        hSourceSplit02
  have hTarget02 :
      z180K30ProjectiveD6FallbackTargetTailV97B02.Perm z180K30ProjectiveD6FallbackTargetRemainderV97B02 := by
    change (z180K30ProjectiveD6FallbackTargetBucketV97B02 ++ z180K30ProjectiveD6FallbackTargetTailV97B03).Perm _
    exact
      ((List.Perm.refl z180K30ProjectiveD6FallbackTargetBucketV97B02).append hTarget03).trans
        hTargetSplit02
  have hBuckets02 :
      z180K30ProjectiveD6FallbackSourceTailV97B02.Perm z180K30ProjectiveD6FallbackTargetTailV97B02 := by
    change (z180K30ProjectiveD6FallbackSourceBucketV97B02 ++ z180K30ProjectiveD6FallbackSourceTailV97B03).Perm
      (z180K30ProjectiveD6FallbackTargetBucketV97B02 ++ z180K30ProjectiveD6FallbackTargetTailV97B03)
    exact
      z180_k30_projective_d6_fallback_bucket_v97_b02.append hBuckets03
  have hSourceSplit01 :
      (z180K30ProjectiveD6FallbackSourceBucketV97B01 ++ z180K30ProjectiveD6FallbackSourceRemainderV97B02).Perm
        z180K30ProjectiveD6FallbackSourceRemainderV97B01 := by
    simpa only [z180K30ProjectiveD6FallbackSourceBucketV97B01, z180K30ProjectiveD6FallbackSourceRemainderV97B02] using
      (List.filter_append_perm
        (z180K30ProjectiveD6FallbackPredicateV97 1)
        z180K30ProjectiveD6FallbackSourceRemainderV97B01)
  have hTargetSplit01 :
      (z180K30ProjectiveD6FallbackTargetBucketV97B01 ++ z180K30ProjectiveD6FallbackTargetRemainderV97B02).Perm
        z180K30ProjectiveD6FallbackTargetRemainderV97B01 := by
    simpa only [z180K30ProjectiveD6FallbackTargetBucketV97B01, z180K30ProjectiveD6FallbackTargetRemainderV97B02] using
      (List.filter_append_perm
        (z180K30ProjectiveD6FallbackPredicateV97 1)
        z180K30ProjectiveD6FallbackTargetRemainderV97B01)
  have hSource01 :
      z180K30ProjectiveD6FallbackSourceTailV97B01.Perm z180K30ProjectiveD6FallbackSourceRemainderV97B01 := by
    change (z180K30ProjectiveD6FallbackSourceBucketV97B01 ++ z180K30ProjectiveD6FallbackSourceTailV97B02).Perm _
    exact
      ((List.Perm.refl z180K30ProjectiveD6FallbackSourceBucketV97B01).append hSource02).trans
        hSourceSplit01
  have hTarget01 :
      z180K30ProjectiveD6FallbackTargetTailV97B01.Perm z180K30ProjectiveD6FallbackTargetRemainderV97B01 := by
    change (z180K30ProjectiveD6FallbackTargetBucketV97B01 ++ z180K30ProjectiveD6FallbackTargetTailV97B02).Perm _
    exact
      ((List.Perm.refl z180K30ProjectiveD6FallbackTargetBucketV97B01).append hTarget02).trans
        hTargetSplit01
  have hBuckets01 :
      z180K30ProjectiveD6FallbackSourceTailV97B01.Perm z180K30ProjectiveD6FallbackTargetTailV97B01 := by
    change (z180K30ProjectiveD6FallbackSourceBucketV97B01 ++ z180K30ProjectiveD6FallbackSourceTailV97B02).Perm
      (z180K30ProjectiveD6FallbackTargetBucketV97B01 ++ z180K30ProjectiveD6FallbackTargetTailV97B02)
    exact
      z180_k30_projective_d6_fallback_bucket_v97_b01.append hBuckets02
  have hSourceSplit00 :
      (z180K30ProjectiveD6FallbackSourceBucketV97B00 ++ z180K30ProjectiveD6FallbackSourceRemainderV97B01).Perm
        z180K30ProjectiveD6FallbackSourceRemainderV97B00 := by
    simpa only [z180K30ProjectiveD6FallbackSourceBucketV97B00, z180K30ProjectiveD6FallbackSourceRemainderV97B01] using
      (List.filter_append_perm
        (z180K30ProjectiveD6FallbackPredicateV97 0)
        z180K30ProjectiveD6FallbackSourceRemainderV97B00)
  have hTargetSplit00 :
      (z180K30ProjectiveD6FallbackTargetBucketV97B00 ++ z180K30ProjectiveD6FallbackTargetRemainderV97B01).Perm
        z180K30ProjectiveD6FallbackTargetRemainderV97B00 := by
    simpa only [z180K30ProjectiveD6FallbackTargetBucketV97B00, z180K30ProjectiveD6FallbackTargetRemainderV97B01] using
      (List.filter_append_perm
        (z180K30ProjectiveD6FallbackPredicateV97 0)
        z180K30ProjectiveD6FallbackTargetRemainderV97B00)
  have hSource00 :
      z180K30ProjectiveD6FallbackSourceTailV97B00.Perm z180K30ProjectiveD6FallbackSourceRemainderV97B00 := by
    change (z180K30ProjectiveD6FallbackSourceBucketV97B00 ++ z180K30ProjectiveD6FallbackSourceTailV97B01).Perm _
    exact
      ((List.Perm.refl z180K30ProjectiveD6FallbackSourceBucketV97B00).append hSource01).trans
        hSourceSplit00
  have hTarget00 :
      z180K30ProjectiveD6FallbackTargetTailV97B00.Perm z180K30ProjectiveD6FallbackTargetRemainderV97B00 := by
    change (z180K30ProjectiveD6FallbackTargetBucketV97B00 ++ z180K30ProjectiveD6FallbackTargetTailV97B01).Perm _
    exact
      ((List.Perm.refl z180K30ProjectiveD6FallbackTargetBucketV97B00).append hTarget01).trans
        hTargetSplit00
  have hBuckets00 :
      z180K30ProjectiveD6FallbackSourceTailV97B00.Perm z180K30ProjectiveD6FallbackTargetTailV97B00 := by
    change (z180K30ProjectiveD6FallbackSourceBucketV97B00 ++ z180K30ProjectiveD6FallbackSourceTailV97B01).Perm
      (z180K30ProjectiveD6FallbackTargetBucketV97B00 ++ z180K30ProjectiveD6FallbackTargetTailV97B01)
    exact
      z180_k30_projective_d6_fallback_bucket_v97_b00.append hBuckets01
  exact hSource00.symm.trans (hBuckets00.trans hTarget00)

end Fuglede.Z180K30ExceptionalRawV2
