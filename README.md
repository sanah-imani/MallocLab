# MallocLab

A 64-bit struct-based segregated list memory allocator with a minimum-sized block of 16 bytes. There is a prologue and epilogue block at the start of the heap and the blocks are 8-byte aligned (payload aligned at 16-bytes). The blocks have an 8-byte header, footer (only for free blocks) and a next (and sometimes prev) block pointers when unallocated and an 8-byte header and a request-sized payload. The sizes of the blocks are 16-byte multiples.
