From mathcomp.ssreflect Require Import ssreflect ssrfun ssrbool ssrnat.
Structure semigrp  :=
  SemiGroup {
      carrier: Type;
      add: carrier->carrier->carrier;
      _add_assoc: associative add
    }.

Definition nat_SemiGroup := SemiGroup nat addn addnA.

Fail Check add _ 4.
Canonical Structure nat_SemiGroup.
Check add _ 4.
