(* Lightweight thread library for Objective Caml
 * http://www.ocsigen.org/lwt
 * Interface Lwt_engine
 * Copyright (C) 2011 Jérémie Dimino
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

(** Lwt unix main loop engine *)

(** {6 Events} *)

type event
  (** Type of events. An event represent a callback registered to be
      called when some event occurs. *)

val stop_event : event -> unit
  (** [stop_event event] stops the given event. *)

val fake_event : event
  (** Event which does nothing when stopped. *)

(** {6 Event loop functions} *)

val iter : bool -> unit
  (** [iter block] performs one iteration of the main loop. If [block]
      is [true] the function must blocks until one event become
      available, otherwise it should just check for available events
      and return immediatly. *)

val on_readable : Unix.file_descr -> (event -> unit) -> event
  (** [on_readable fd f] calls [f] each time [fd] becomes readable. *)

val on_writable : Unix.file_descr -> (event -> unit) -> event
  (** [on_readable fd f] calls [f] each time [fd] becomes writable. *)

val on_timer : float -> bool -> (event -> unit) -> event
  (** [on_timer delay repeat f] calls [f] one time after [delay]
      seconds. If [repeat] is [true] then [f] is called each [delay]
      seconds, otherwise it is called only one time. *)

(** {6 Engines} *)

(** An engine represent a set of functions used to register different
    kind of callbacks for different kind of events. *)

(** Type of engines. *)
class virtual t : object
  method destroy : unit
    (** Destroy the engine and free its associated resources. *)

  method copy : t -> unit
    (** [copy engine] copy all events from the current engine to
        [engine]. Note that timers are reset in the destination
        engine, i.e. if a timer with a delay of 2 seconds was
        registered 1 second ago it will occurs in 2 seconds in the
        destination engine. *)

  (** {6 Event loop methods} *)

  method virtual iter : bool -> unit
  method on_readable : Unix.file_descr -> (event -> unit) -> event
  method on_writable : Unix.file_descr -> (event -> unit) -> event
  method on_timer : float -> bool -> (event -> unit) -> event

  (** {6 Backend methods} *)

  (** Notes:

      - the callback passed to register methods is of type [unit ->
      unit] and not [event -> unit]
      - register methods returns a lazy value which unregister the
      event when forced
  *)

  method virtual private cleanup : unit
    (** Cleanup resources associated to the engine. *)

  method virtual private register_readable : Unix.file_descr -> (unit -> unit) -> unit Lazy.t
  method virtual private register_writable : Unix.file_descr -> (unit -> unit) -> unit Lazy.t
  method virtual private register_timer : float -> bool -> (unit -> unit) -> unit Lazy.t
end

(** {6 Predefined engines} *)

type ev_loop
  (** Type of libev loops. *)

(** Engine based on libev. *)
class libev : object
  inherit t

  val loop : ev_loop
    (** The libev loop used for this engine. *)

  method loop : ev_loop
    (** Returns [loop]. *)

  method iter : bool -> unit
  method private cleanup : unit
  method private register_readable : Unix.file_descr -> (unit -> unit) -> unit Lazy.t
  method private register_writable : Unix.file_descr -> (unit -> unit) -> unit Lazy.t
  method private register_timer : float -> bool -> (unit -> unit) -> unit Lazy.t
end

(** Engine based on select. *)
class select : object
  inherit t

  method iter : bool -> unit
  method private cleanup : unit
  method private register_readable : Unix.file_descr -> (unit -> unit) -> unit Lazy.t
  method private register_writable : Unix.file_descr -> (unit -> unit) -> unit Lazy.t
  method private register_timer : float -> bool -> (unit -> unit) -> unit Lazy.t
end

(** {6 The current engine} *)

val get : unit -> t
  (** [get ()] returns the engine currently in use. *)

val set : t -> unit
  (** [set engine] replaces the current engine by the given one. All
      events from the current engine are copied to the new one. *)