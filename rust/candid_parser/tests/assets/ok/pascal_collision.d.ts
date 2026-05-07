import type { Principal } from '@icp-sdk/core/principal';
import type { ActorMethod } from '@icp-sdk/core/agent';
import type { IDL } from '@icp-sdk/core/candid';

/**
 * PascalCase output collides with a verbatim env key — foo_baz should fall back.
 */
export type FooBaz = bigint;
export type fooBar = string;
/**
 * Two names that map to the same PascalCase form — first alphabetically wins, second falls back.
 */
export type foo_bar = bigint;
export type foo_baz = string;

