"""
smr - Safe Memory Reclamation (backward compatibility module)

This module re-exports from _smr_ibr for backward compatibility.
New code should import directly from _smr_ibr or _smr_debra.
"""

from concurrent_collections._smr_ibr import (
    SMRDomain,
    SMRGuard,
    get_default_smr,
    IBRDomain,
    IBRGuard,
    SMRProfiler,
    SMRProfilerReport,
    get_default_ibr,
    RetiredNode,
)

__all__ = [
    "SMRDomain",
    "SMRGuard",
    "get_default_smr",
    "IBRDomain",
    "IBRGuard",
    "SMRProfiler",
    "SMRProfilerReport",
    "get_default_ibr",
    "RetiredNode",
]
