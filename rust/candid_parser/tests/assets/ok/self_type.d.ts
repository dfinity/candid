import type { Principal } from '@icp-sdk/core/principal';
import type { ActorMethod } from '@icp-sdk/core/agent';
import type { IDL } from '@icp-sdk/core/candid';

/**
 * Verbatim "Self" in env — falls back to "Self_" to avoid shadowing pp_actor output.
 */
export type Self = string;
/**
 * "self" would PascalCase to "Self" which is reserved — falls back to "self".
 */
export type self = bigint;

