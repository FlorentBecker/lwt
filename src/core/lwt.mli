(* Lightweight thread library for OCaml
 * http://www.ocsigen.org/lwt
 * Interface Lwt
 * Copyright (C) 2005-2008 Jérôme Vouillon
 * Laboratoire PPS - CNRS Université Paris Diderot
 *               2009-2012 Jérémie Dimino
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as
 * published by the Free Software Foundation, with linking exceptions;
 * either version 2.1 of the License, or (at your option) any later
 * version. See COPYING file for details.
 *
 * This program is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA
 * 02111-1307, USA.
 *)

(* TODO Link to some tutorial once it exists? *)
(** Promises.

    This module defines {e promises}: values that may become determined in the
    future. A promise that can become determined with values of type ['a] has
    type ['a Lwt.t]. A promise is always in one of three states:

    - {e resolved}, and containing a read-only value of type ['a],
    - {e failed}, and containing a read-only exception (of type [exn]), or
    - {e pending}, in which case it may become resolved or failed in the future.

    Many functions in Lwt create promises. For example, {!Lwt_unix.write} starts
    a concurrent [write] system call in the background, and gives you a promise
    that will resolve when that system call completes. You can get the result by
    waiting on the promise with the [let%lwt] construct:

{[
let () =
  Lwt_main.run begin
    let%lwt bytes_written =
      Lwt_unix.write Lwt_unix.stdout "Hello! " 0 (Bytes.length "Hello! ") in
    let%lwt () = Lwt_io.printf "Wrote %i bytes!\n" bytes_written in
    Lwt.return_unit
  end
  (* ocamlfind opt -linkpkg -package lwt.unix -package lwt.ppx example.ml *)
]}

   That prints: {v Hello! Wrote 7 bytes! v} The surrounding call to
   {!Lwt_main.run} drives the Lwt code and forces it to run to completion.
   Without {!Lwt_main.run}, the program would create several promises, but then
   exit immediately without waiting for any of them. You call {!Lwt_main.run}
   once, at the top level of your program, if you are targeting a Unix or
   Windows system, but it is not necessary when compiling to JavaScript. *)



(** {2 Basics} *)

type +'a t
(** Promises that resolve with values of type ['a]. *)

type -'a u
(** Resolvers for promises of type ['a t]. *)

(** {3 Creating} *)

val wait : unit -> 'a t * 'a u
(** [Lwt.wait ()] gives a pair [(promise, resolver)]. The promise is pending
    until something calls [Lwt.wakeup_later resolver v], at which point the
    promise is resolved with [v]. It is also possible to fail the promise with
    [exn] by calling [Lwt.wakeup_later_exn resolver exn]. Promises created with
    [Lwt.wait] cannot be canceled; see {!Lwt.task} for cancelable promises.

    In ordinary, high-level usage of Lwt, you call Lwt functions other than
    [Lwt.wait] to get interesting promises. However, those functions internally
    use [Lwt.wait] or {!Lwt.task}. They start some background work, return the
    new promise immediately, and hold on to the resolver. When the work is
    finished, they use the resolver to resolve the promise.

    Sometimes, you need to create a promise directly on your own. As a simple
    example, here is an overly elaborate way to pass around [42]:

{[
let () =
  let promise, resolver = Lwt.wait () in
  let wait_for_resolve =
    let%lwt answer = promise in
    let%lwt () = Lwt_io.printf "The answer is: %i\n" answer in
    Lwt.return_unit
  in
  Lwt.wakeup_later resolver 42;   (* Resolve the promise. *)
  Lwt_main.run wait_for_resolve
(* ocamlfind opt -linkpkg -package lwt.unix -package lwt.ppx example.ml *)
]} *)

(** {3 Resolving} *)

val wakeup_later : 'a u -> 'a -> unit
(** [Lwt.wakeup_later resolver v] resolves the promise associated with
    [resolver] with the value [v]. See {!Lwt.wait}.

    A promise can only be resolved once. Calling [Lwt.wakeup_later], or related
    functions, more than once on the same resolver raises [Invalid_argument]. *)

val wakeup_later_exn : 'a u -> exn -> unit
(** Like {!Lwt.wakeup_later}, but fails the promise with the given exception
    instead. *)

(** {3 Waiting} *)

(* TODO Backtraces. *)
val bind : 'a t -> ('a -> 'b t) -> 'b t
(** [Lwt.bind promise then_] schedules [then_] to be called when [promise]
    resolves. [Lwt.bind] immediately evaluates to [promise'], which is resolved
    as follows:

    - First, [promise'] waits for [promise]. If [promise] fails with [exn],
      [promise'] also fails with [exn], and [then_] is never called.
    - If [promise] resolves successfully with value [v], [then_ v] is called. If
      either that call, or the promise it returns, fail with [exn], [promise']
      fails with [exn] as well.
    - If the promise [then_ v] resolves successfully with [v'], [promise']
      resolves with [v'].
    - Note that this behavior is the same even if [promise] has already resolved
      or failed.

    [Lwt.bind] is Lwt's basic sequencing operation. It is how you cause code to
    run in the future. However, a sequence of calls to [Lwt.bind] is a bit
    awkward to maintain when used directly, because of the need to balance
    parentheses. For this reason, Lwt provides the [let%lwt] construct, which
    is pronounced "bind" and desugars to [Lwt.bind]:

{[
let () =
  Lwt_main.run begin
    let%lwt () = Lwt_unix.sleep 5. in
    let%lwt () =
      Lwt_io.printl "Slept 5 seconds more than the author of this manual." in
    Lwt.return_unit
  end
(* ocamlfind opt -linkpkg -package lwt.unix -package lwt.ppx example.ml *)
]}

    That desugars to:

{[
let () =
  Lwt_main.run begin
    Lwt.bind (Lwt_unix.sleep 5.) (fun () ->
    Lwt.bind
      (Lwt_io.printl "Slept 5 seconds more than the author of this manual.")
      (fun () ->
    Lwt.return_unit))   (* <-- those parens will get annoying. *)
  end
(* ocamlfind opt -linkpkg -package lwt.unix example.ml *)
]}

    [let%lwt] is the recommended way to write Lwt code. It requires package
    [lwt.ppx]. An alternative syntactic sugar for [Lwt.bind] is the infix
    operator {!Lwt.(>>=)}:

{[
open Lwt.Infix
let () =
  Lwt_main.run begin
    Lwt_unix.sleep 5. >>= fun () ->
    Lwt_io.printl
      "Slept 5 seconds more than the author of this manual." >>= fun () ->
    Lwt.return_unit
  end
(* ocamlfind opt -linkpkg -package lwt.unix example.ml *)
]}

    It is normal to schedule multiple [then_] functions on a single promise.
    They will all be called when the promise resolves, in some arbitrary
    order. Here is a simple "fork-join" with Lwt:

{[
let () =
  Lwt_main.run begin
    let sleeping = Lwt_unix.sleep 5. in
    let waiting_1 =
      let%lwt () = sleeping in
      let%lwt () = Lwt_io.printl "Will this run first?" in
      Lwt.return_unit
    in
    let waiting_2 =
      let%lwt () = sleeping in
      let%lwt () = Lwt_io.printl "Or this?" in
      Lwt.return_unit
    in
    Lwt.join [waiting_1; waiting_2]
  end
(* ocamlfind opt -linkpkg -package lwt.unix -package lwt.ppx example.ml *)
]}

    The {!Lwt.join} just waits for both promises to resolve.

 *)

(** {3 Trivial promises} *)

val return : 'a -> 'a t
(** Creates a promise that has already resolved with the given value.

    This function is used mostly for satisfying the type system: when a promise
    is expected, but you have a regular value, apply [Lwt.return] to wrap it. A
    typical scenario is wrapping a value at the end of a {!Lwt.bind}, a.k.a.
    [let%lwt], because the [then_] function has to evaluate to a promise:

{[
let () =
  Lwt_main.run begin
    let%lwt bytes_written =
      Lwt_unix.(write stdout) "Hello " 0 (Bytes.length "Hello ") in
    let%lwt bytes_written' =
      Lwt_unix.(write stdout) "world!" 0 (Bytes.length "world!") in
    Lwt.return (bytes_written + bytes_written')
  end
  |> Printf.printf "\nWrote %i bytes!\n"
(* ocamlfind opt -linkpkg -package lwt.unix -package lwt.ppx example.ml *)
]}

    Where performance matters, some allocations can be saved by using
    {{:#3_Preallocatedpromises} pre-allocated promises}. A future version of Lwt
    might make this unnecessary by performing the optimization automatically.

    Note that an expression like [Lwt.return (compute ())] does not create a
    promise that "waits for" [compute ()]. Instead, it first runs [compute ()]
    to completion, and only then wraps its result in an already-resolved
    promise. This expression is therefore pointless:

{[
let%lwt result = Lwt.return (compute ()) in
(* do something with result *)
]}

    and can be reduced to:

{[
let result = compute () in
(* do something with result *)
]}

    For creating unresolved promises that {e are} pending on something, see
    {!Lwt.wait} and {!Lwt.task}. *)

(* TODO Add note about how to raise exceptions in Lwt. *)
(* TODO Link to exception handling. *)
val fail : exn -> 'a t
(** Creates a promise that has already failed with the given exception. This is
    analogous to {!Lwt.return}. *)



(** {2 Exceptions} *)

(* TODO Note syntax. *)
(* TODO Warn about using regular try. *)
val catch : (unit -> 'a t) -> (exn -> 'a t) -> 'a t
(** [Lwt.catch f handler] tries to resolve the promise [f ()], and runs
    [handler exn] if [f ()] fails. In more detail, it evaluates to [promise],
    which is resolved as follows:

    - If applying [f ()] results in a promise, and that promise resolves with
      value [v], then the outer [promise] resolves with [v] as well.
    - If applying [f ()] raises [exn], or results in a promise, but that promise
      fails with [exn], then [handler exn] is applied.
    - If [handler exn] raises [exn'], or results in a promise, and that promise
      fails with [exn'], the outer [promise] fails with [exn'].
    - Otherwise, if [handler exn] results in a promise, and that promise
      resolves with value [v'], the outer promise resolves with [v'].

    This function is typically written using the [try%lwt] syntax:

{[
let () =
  Lwt_main.run begin
    try%lwt
      let%lwt () = Lwt_io.printl "About to fail!" in
      raise (Failure "no reason")
    with Failure reason ->
      let%lwt () = Lwt_io.printf "Failed for %s" reason in
      Lwt.return_unit
  end
(* ocamlfind opt -linkpkg -package lwt.unix -package lwt.ppx example.ml *)
]}

    That desugars to:

{[
let () =
  Lwt_main.run begin
    Lwt.catch
      (fun () ->
        let%lwt () = Lwt_io.printl "About to fail!" in
        raise (Failure "no reason")
      (function
        | Failure reason ->
          let%lwt () = Lwt_io.printf "Failed for %s" reason in
          Lwt.return_unit
        | exn -> Lwt.fail exn)
  end
(* ocamlfind opt -linkpkg -package lwt.unix -package lwt.ppx example.ml *)
]}

    It is important not to use the ordinary [try] to handle exceptions raised
    while a promise is being resolved. Let's take a program similar to the first
    example, but replace [try%lwt] with [try], and consider what would happen:

{[
let () =
  Lwt_main.run begin
    try
      let%lwt () = Lwt_unix.sleep 1. in
      raise (Failure "no reason")
    with Failure reason ->
      let%lwt () = Lwt_io.printf "Failed for %s." reason in
      Lwt.return_unit
  end
(* ocamlfind opt -linkpkg -package lwt.unix -package lwt.ppx example.ml *)
]}

    The first thing this program does is evaluate [Lwt_unix.sleep 1.]. That
    creates a pending promise. The [let%lwt () = ... in] wraps that in another
    pending promise [p], which will fail {e later}, once the [sleep] resolves.
    No exception occurrs while {e creating} [p], so the [try] evaluates to [p],
    and is dismissed. [p] is passed to {!Lwt_main.run}, which runs it to
    completion. [p] fails after one second, but, because there is no handler,
    the failure aborts the program, instead of printing
    ["Failed for no reason."].

    You can replace the [try] with [try%lwt], and the program will have the
    expected behavior. The general rule is: [try] is for exceptions raised while
    promises are being created, and [try%lwt] is for exceptions raised while
    promises are being created or resolved. You almost always want the
    latter. *)

(* TODO What happens if after fails? *)
val finalize : (unit -> 'a t) -> (unit -> unit t) -> 'a t
(** [Lwt.finalize f then_] resolves [f ()], then resolves [then_] no matter
    whether [f ()] resolves or fails. In more detail, it evaluates to [promise],
    which is resolved as follows:

    - If applying [f ()] results in a promise, and that promise resolves with
      value [v], and [then_ ()] also resolves, [promise] resolves with [v].
    - If applying [f ()] raises [exn], or results in a promise, and that promise
      fails with [exn], and [then_ ()] resolves, [promise] fails with [exn].
    - No matter the behavior of [f ()], if [then_ ()] raises [exn'] or results
      in a promise, but the promise fails with [exn'], [promise] fails with
      [exn'].

    This function can be used with the [[%finally]] syntax:

{[
let () =
  Lwt_main.run begin
    Random.self_init ();
    (if Random.bool () then raise (Failure "Bad luck!") else Lwt.return_unit)
    [%finally Lwt_io.printl "This always runs."]
  end
(* ocamlfind opt -linkpkg -package lwt.unix -package lwt.ppx example.ml *)
]}

    That desugars to:

{[
let () =
  Lwt_main.run begin
    Random.self_init ();
    Lwt.finalize
      (fun () ->
        if Random.bool () then raise (Failure "Bad luck!") else Lwt.return_unit)
      (fun () -> Lwt_io.printl "This always runs.")
  end
(* ocamlfind opt -linkpkg -package lwt.unix -package example.ml *)
]} *)



(** {2 Concurrency} *)

val async : (unit -> 'a t) -> unit
(** [Lwt.async f] applies [f ()], and adds the resulting promise to Lwt's
    internal scheduler. This basically "forks" a "task" that you cannot wait on.
    The promise [f ()] doesn't have to resolve: it might be an infinite loop.

    For example, this will print nonsense about five times:

{[
let () =
  Lwt_main.run begin
    Lwt.async begin fun () ->
      let rec loop () =
        let%lwt () = Lwt_io.printl "Nananana..." in
        let%lwt () = Lwt_unix.sleep 1. in
        loop ()
      in
      loop ()
    end;
    let%lwt () = Lwt_unix.sleep 4.5 in
    Lwt.return_unit
  end
(* ocamlfind opt -linkpkg -package lwt.unix -package lwt.ppx example.ml *)
]}

    If [f ()] raises an exception, or the promise [f ()] fails, that is a
    programming error, because there is no graceful way for the program to
    handle the exception: the exception has nowhere to go. It is passed to
    {!Lwt.async_exception_hook}, which terminates the program by default.

    Note that the promise [f ()] is run concurrently, but not in parallel, with
    the code that called [Lwt.async]. Unless [f ()] or the calling code do I/O,
    multitasking between them is cooperative, and both are run in a single
    system thread. For running code in multiple threads, see module
    {!Lwt_preemptive}. Note further, however, that current versions of OCaml
    don't allow multiple system threads to run OCaml code in parallel. However,
    two threads can run code in parallel if at least one of them calls C code
    and releases the OCaml runtime lock. *)

(* TODO What was that about storage unchanged? *)
val join : unit t list -> unit t
(** [Lwt.join promises] waits for all [promises] to resolve or fail. Then, if
    all promises resolve, [Lwt.join promises] resolves with [()]. Otherwise, if
    at least one promise fails, [Lwt.join promises] fails with the same
    exception as the first promise to fail. If two or more promises had already
    failed when passed to [Lwt.join], [Lwt.join promises] chooses one
    arbitrarily to be the first.

{[
let () =
  Lwt_main.run begin
    let sleep_1 =
      let%lwt () = Lwt_io.print "This program sleeps only 1 second: " in
      let%lwt () = Lwt_unix.sleep 1. in
      Lwt.return_unit
    in
    let sleep_2 =
      let%lwt () = Lwt_io.printl "the promises are resolved in parallel." in
      let%lwt () = Lwt_unix.sleep 1. in
      Lwt.return_unit
    in
    Lwt.join [sleep_1; sleep_2]
  end
(* ocamlfind opt -linkpkg -package lwt.unix -package lwt.ppx example.ml *)
]}

    Note that it is only the I/O in these two promises that is resolved in
    parallel. All the code is run in a single OCaml thread. If both promises ran
    only code, they would be resolved entirely in series, though in an aribtrary
    order.

    [Lwt.join [sleep_1; sleep_2]] can be written [sleep_1 <&> sleep_2], if you
    [open Lwt.Infix]. See {!Lwt.(<&>)}. *)

(* TODO What was that about storage unchanged? *)
val choose : 'a t list -> 'a t
(** [choose promises] waits for any promise in [promises] to resolve or fail. It
    then resolves or fails the same as that promise. If several promises have
    already resolved or failed when [choose] is called, one is chosen
    arbitrarily.

    [Lwt.choose [t; t']] can also be written [t <?> t'], if you
    [open Lwt.Infix]. See {!Lwt.(<?>)}. *)

(* TODO What was that about storage unchanged? *)
(* TODO Is it really true that this fails if *any* promise in l fails? Or just
   the ones that were seen when nchoose was called? *)
val nchoose : 'a t list -> 'a list t
(** [nchoose promises] is like {!Lwt.choose}, but if several promises have
    already resolved or failed, all are returned. *)

val nchoose_split : 'a t list -> ('a list * 'a t list) t
(** [nchoose_split promises] is like {!Lwt.nchoose} but also retrurns the list
    of promises that have not yet resolved or failed. *)

val ignore_result : 'a t -> unit
(** [ignore_result t] behaves as follows:

    - if [t] has completed with a result, [ignore_result t] does nothing,
    - if [t] has completed with an exception, [ignore_result t] raises the
      exception,
    - if [t] has not completed, [ignore_result t] evaluates to [()] immediately,
      but if [t] completes later with an exception, it will be given to
      {!async_exception_hook}.

    Note that this means [ignore_result t] does not wait for [t] to complete. If
    you need to wait, use [t >>= fun _ -> (* ...after t... *)]. *)

val async_exception_hook : (exn -> unit) ref
(** [!Lwt.async_exception_hook exn] is called when [exn] is raised by some
    computation, but there is no promise that Lwt can fail with [exn].

    The typical example is when you call [Lwt.async computation], and
    [computation ()] raises an exception: since {!Lwt.async} does not produce a
    promise, this exception has "nowhere to go," and is given to
    [!Lwt.async_exception_hook].

    All such situations are programming errors. The default behavior of this
    function is to print an error message and exit the program.

    If you are writing an application, you can replace this reference with
    another function. If writing a library, you should not modify it. *)



(** {2 Sleeping and resuming} *)

val wakeup : 'a u -> 'a -> unit
  (** [wakeup t e] makes the sleeping thread [t] terminate and return
      the value of the expression [e]. *)

val wakeup_exn : 'a u -> exn -> unit
  (** [wakeup_exn t e] makes the sleeping thread [t] fail with the
      exception [e]. *)

val waiter_of_wakener : 'a u -> 'a t
  (** Returns the thread associated to a wakener. *)

type +'a result = ('a, exn) Result.result
  (** Either a value of type ['a], either an exception.

      This type is defined as [('a, exn) Result.result] since 2.6.0. *)

val make_value : 'a -> 'a result
  [@@ocaml.deprecated
    " Use Result.Ok, which is the same as Ok since OCaml 4.03."]
  (** [value x] creates a result containing the value [x].
      @deprecated Since 2.6.0. Use {!Result.Ok} *)

val make_error : exn -> 'a result
  [@@ocaml.deprecated
    " Use Result.Error, which is the same as Error since OCaml 4.03."]
  (** [error e] creates a result containing the exception [e].
      @deprecated Since 2.6.0. Use {!Result.Error} *)

val of_result : 'a result -> 'a t
  (** Returns a thread from a result. *)

val wakeup_result : 'a u -> 'a result -> unit
  (** [wakeup_result t r] makes the sleeping thread [t] terminate with
      the result [r]. *)

val wakeup_later_result : 'a u -> 'a result -> unit
  (** Same as {!wakeup_result} but it is not guaranteed that the
      thread will be woken up immediately. *)

(** {2 Threads state} *)

(** State of a thread *)
type 'a state =
  | Return of 'a
      (** The thread which has successfully terminated *)
  | Fail of exn
      (** The thread raised an exception *)
  | Sleep
      (** The thread is sleeping *)

val state : 'a t -> 'a state
  (** [state t] returns the state of a thread *)

val is_sleeping : 'a t -> bool
  (** [is_sleeping t] returns [true] iff [t] is sleeping. *)

(** {2 Cancelable threads} *)

(** Cancelable threads are the same as regular threads except that
    they can be canceled. *)

exception Canceled
  (** Canceled threads fails with this exception *)

val task : unit -> 'a t * 'a u
  (** [task ()] is the same as [wait ()] except that threads created
      with [task] can be canceled. *)

val on_cancel : 'a t -> (unit -> unit) -> unit
  (** [on_cancel t f] executes [f] when [t] is canceled. [f] will be
      executed before all other threads waiting on [t].

      If [f] raises an exception it is given to
      {!async_exception_hook}. *)

val add_task_r : 'a u Lwt_sequence.t -> 'a t
  (** [add_task_r seq] creates a sleeping thread, adds its wakener to
      the right of [seq] and returns its waiter. When the thread is
      canceled, it is removed from [seq]. *)

val add_task_l : 'a u Lwt_sequence.t -> 'a t
  (** [add_task_l seq] creates a sleeping thread, adds its wakener to
      the left of [seq] and returns its waiter. When the thread is
      canceled, it is removed from [seq]. *)

val cancel : 'a t -> unit
  (** [cancel t] cancels the threads [t]. This means that the deepest
      sleeping thread created with [task] and connected to [t] is
      woken up with the exception {!Canceled}.

      For example, in the following code:

      {[
        let waiter, wakener = task () in
        cancel (waiter >> printl "plop")
      ]}

      [waiter] will be woken up with {!Canceled}.
  *)

val pick : 'a t list -> 'a t
  (** [pick l] is the same as {!choose}, except that it cancels all
      sleeping threads when one terminates.

      Note: {!pick} leaves the local values of the current thread
      unchanged. *)

val npick : 'a t list -> 'a list t
  (** [npick l] is the same as {!nchoose}, except that it cancels all
      sleeping threads when one terminates.

      Note: {!npick} leaves the local values of the current thread
      unchanged. *)

val protected : 'a t -> 'a t
  (** [protected thread] creates a new cancelable thread which behave
      as [thread] except that cancelling it does not cancel
      [thread]. *)

val no_cancel : 'a t -> 'a t
  (** [no_cancel thread] creates a thread which behave as [thread]
      except that it cannot be canceled. *)

(** {2 Pause} *)

val pause : unit -> unit t
  (** [pause ()] is a sleeping thread which is wake up on the next
      call to {!wakeup_paused}. A thread created with [pause] can be
      canceled. *)

val wakeup_paused : unit -> unit
  (** [wakeup_paused ()] wakes up all threads which suspended
      themselves with {!pause}.

      This function is called by the scheduler, before entering the
      main loop. You usually do not have to call it directly, except
      if you are writing a custom scheduler.

      Note that if a paused thread resumes and pauses again, it will not
      be woken up at this point. *)

val paused_count : unit -> int
  (** [paused_count ()] returns the number of currently paused
      threads. *)

val register_pause_notifier : (int -> unit) -> unit
  (** [register_pause_notifier f] register a function [f] that will be
      called each time pause is called. The parameter passed to [f] is
      the new number of threads paused. It is usefull to be able to
      call {!wakeup_paused} when there is no scheduler *)

(** {2 Misc} *)

val on_success : 'a t -> ('a -> unit) -> unit
  (** [on_success t f] executes [f] when [t] terminates without
      failing. If [f] raises an exception it is given to
      {!async_exception_hook}. *)

val on_failure : 'a t -> (exn -> unit) -> unit
  (** [on_failure t f] executes [f] when [t] terminates and fails. If
      [f] raises an exception it is given to
      {!async_exception_hook}. *)

val on_termination : 'a t -> (unit -> unit) -> unit
  (** [on_termination t f] executes [f] when [t] terminates. If [f]
      raises an exception it is given to {!async_exception_hook}. *)

val on_any : 'a t -> ('a -> unit) -> (exn -> unit) -> unit
  (** [on_any t f g] executes [f] or [g] when [t] terminates. If [f]
      or [g] raises an exception it is given to
      {!async_exception_hook}. *)

(** Infix operators. You should open only this module. *)
module Infix : sig

  val (>>=) : 'a t -> ('a -> 'b t) -> 'b t
  (** [t >>= f] is an alternative notation for [bind t f]. *)

  val (=<<) : ('a -> 'b t) -> 'a t -> 'b t
  (** [f =<< t] is [t >>= f] *)

  val (>|=) : 'a t -> ('a -> 'b) -> 'b t
  (** [m >|= f] is [map f m] *)

  val (=|<) : ('a -> 'b) -> 'a t -> 'b t
  (** [f =|< m] is [map f m] *)

  val ( <?> ) : 'a t -> 'a t -> 'a t
  (** [t <?> t'] is the same as [choose [t; t']] *)

  val ( <&> ) : unit t -> unit t -> unit t
  (** [t <&> t'] is the same as [join [t; t']] *)
end



(** {2 Storage}

    Lwt is not a threading library. However, a sequence of binds can be {e very}
    loosely thought of as some kind of "thread":

{[
let%lwt () = Lwt_unix.sleep 5. in
let%lwt s = Lwt_io.read stdin in
let%lwt () = Lwt_io.write stdout s in
(* ... *)
]}

    By analogy with thread-local storage, it is possible to associate data
    values with such a sequence:

{[
let () =
  let my_key : int Lwt.key = Lwt.new_key () in
  let sequence k =
    Lwt.with_value my_key (Some k) (fun () ->
      let%lwt () = Lwt_io.printf "Executing sequence with k = %i.\n%!" k in
      assert (Lwt.get my_key = Some k);
      let%lwt () = Lwt_unix.sleep 1. in
      let%lwt () = Lwt_io.printf "Executing sequence with k = %i.\n%!" k in
      assert (Lwt.get my_key = Some k);
      Lwt.return_unit)
  in
  Lwt_main.run (Lwt.join [sequence 42; sequence 1337])
(* ocamlfind opt -linkpkg -package lwt.unix -package lwt.ppx example.ml *)
]}

    In the above example, Lwt preserves the values [42] and [1337] associated to
    [my_key] in the respective sequences, even though their execution order is
    interleaved.

    TODO Explain details about when the snapshot happens.

    It is recommended that you avoid using this mechanism whenver possible, and
    prefer explicit variables that are either in scope, or passed around through
    promises. *)

type 'a key
  (** Type of a key. Keys are used to store local values into
      threads. *)

val new_key : unit -> 'a key
  (** [new_key ()] creates a new key. *)

val get : 'a key -> 'a option
  (** [get key] returns the value associated with [key] in the current
      thread. *)

val with_value : 'a key -> 'a option -> (unit -> 'b) -> 'b
  (** [with_value key value f] executes [f] with [value] associated to
      [key]. [key] is restored to its previous value after [f] terminates.

      This function should not be applied within threads created with
      {!Lwt_preemptive.detach}. *)



(** {2 Convenience} *)

(** {3 Waiting} *)

val (>>=) : 'a t -> ('a -> 'b t) -> 'b t
(** [promise >>= after] is the same as [Lwt.bind promise after]. See remarks at
    {!Lwt.bind}. *)

(** {3 Composition} *)

val ( <?> ) : 'a t -> 'a t -> 'a t
(** [t <?> t'] is the same as [choose [t; t']]. See {!Lwt.choose}. *)

val ( <&> ) : unit t -> unit t -> unit t
(** [t <&> t'] is the same as [join [t; t']]. See {!Lwt.join}. *)

(* TODO Permanent anchor for this. *)
(** {3 Pre-allocated promises} *)

val return_unit : unit t
(** Like [Lwt.return ()], but does not allocate a new promise. See
    {!Lwt.return}. *)

val return_none : 'a option t
(** Like [Lwt.return None], but does not allocate a new promise. See
    {!Lwt.return}. *)

val return_nil : 'a list t
(** Like [Lwt.return []], but does not allocate a new promise. See
    {!Lwt.return}. *)

val return_true : bool t
(** Like [Lwt.return true], but does not allocate a new promise. See
    {!Lwt.return}. *)

val return_false : bool t
(** Like [Lwt.return true], but does not allocate a new promise. See
    {!Lwt.return}. *)



(**/**)

(* The functions below are probably not useful for the casual user.
   They provide the basic primitives on which can be built multi-
   threaded libraries such as Lwt_unix. *)

val poll : 'a t -> 'a option
      (* [poll e] returns [Some v] if the thread [e] is terminated and
         returned the value [v].  If the thread failed with some
         exception, this exception is raised.  If the thread is still
         running, [poll e] returns [None] without blocking. *)

val apply : ('a -> 'b t) -> 'a -> 'b t
      (* [apply f e] apply the function [f] to the expression [e].  If
         an exception is raised during this application, it is caught
         and the resulting thread fails with this exception. *)
(* Q: Could be called 'glue' or 'trap' or something? *)

val backtrace_bind : (exn -> exn) -> 'a t -> ('a -> 'b t) -> 'b t
val backtrace_catch : (exn -> exn) -> (unit -> 'a t) -> (exn -> 'a t) -> 'a t
val backtrace_try_bind : (exn -> exn) -> (unit -> 'a t) -> ('a -> 'b t) -> (exn -> 'b t) -> 'b t
val backtrace_finalize : (exn -> exn) -> (unit -> 'a t) -> (unit -> unit t) -> 'a t

val abandon_wakeups : unit -> unit

(**/**)

(**/**)

(* Attic: to place... *)

val fail_with : string -> 'a t
  (** [fail_with msg] is a thread that fails with the exception
      [Failure msg]. *)

val fail_invalid_arg : string -> 'a t
  (** [fail_invalid_arg msg] is a thread that fails with the exception
      [Invalid_argument msg]. *)

val (=<<) : ('a -> 'b t) -> 'a t -> 'b t
  (** [f =<< t] is [t >>= f] *)

val map : ('a -> 'b) -> 'a t -> 'b t
  (** [map f m] maps the result of a thread. This is the same as [bind
      m (fun x -> return (f x))] *)

val (>|=) : 'a t -> ('a -> 'b) -> 'b t
  (** [m >|= f] is [map f m] *)

val (=|<) : ('a -> 'b) -> 'a t -> 'b t
  (** [f =|< m] is [map f m] *)

(** {2 Exceptions handling} *)

val try_bind : (unit -> 'a t) -> ('a -> 'b t) -> (exn -> 'b t) -> 'b t
  (** [try_bind t f g] behaves as [bind (t ()) f] if [t] does not
      fail.  Otherwise, it behaves as the application of [g] to the
      exception associated to [t ()]. *)

val wrap : (unit -> 'a) -> 'a t
  (** [wrap f] calls [f] and transforms the result into an Lwt thread.
      If [f] raises an exception, it is caught and converted to an Lwt
      exception.

      This is actually the same as:

      {[
        try
          return (f ())
        with exn ->
          fail exn
      ]}
  *)

val wrap1 : ('a -> 'b) -> 'a -> 'b t
  (** [wrap1 f x] applies [f] on [x] and returns the result as a
      thread. If the application of [f] to [x] raise an exception it
      is catched and a thread is returned.

      Note that you must use {!wrap} instead of {!wrap1} if the
      evaluation of [x] may raise an exception.

      For example, the following code is incorrect:

      {[
        wrap1 f (Hashtbl.find table key)
      ]}

      and should be written as:

      {[
        wrap (fun () -> f (Hashtbl.find table key))
      ]}
  *)

val wrap2 : ('a -> 'b -> 'c) -> 'a -> 'b -> 'c t
val wrap3 : ('a -> 'b -> 'c -> 'd) -> 'a -> 'b -> 'c -> 'd t
val wrap4 : ('a -> 'b -> 'c -> 'd -> 'e) -> 'a -> 'b -> 'c -> 'd -> 'e t
val wrap5 : ('a -> 'b -> 'c -> 'd -> 'e -> 'f) -> 'a -> 'b -> 'c -> 'd -> 'e -> 'f t
val wrap6 : ('a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'g) -> 'a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'g t
val wrap7 : ('a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'g -> 'h) -> 'a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'g -> 'h t

val return_some : 'a -> 'a option t
  (** [return_some x = return (Some x)] *)

val return_ok : 'a -> ('a, _) Result.result t
  (** [return_ok x] is equivalent to [return (Ok x)].
      @since 2.6.0 *)

val return_error : 'e -> (_, 'e) Result.result t
  (** [return_error x] is equivalent to [return (Error x)].
      @since 2.6.0 *)

(**/**)
