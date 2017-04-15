/*
 *  chidb - a didactic relational database management system
 *
 * This module contains functions to manipulate a B-Tree file. In this context,
 * "BTree" refers not to a single B-Tree but to a "file of B-Trees" ("chidb
 * file" and "file of B-Trees" are essentially equivalent terms).
 *
 * However, this module does *not* read or write to the database file directly.
 * All read/write operations must be done through the pager module.
 *
 */

/*
 *  Copyright (c) 2009-2015, The University of Chicago
 *  All rights reserved.
 *
 *  Redistribution and use in source and binary forms, with or withsend
 *  modification, are permitted provided that the following conditions are met:
 *
 *  - Redistributions of source code must retain the above copyright notice,
 *    this list of conditions and the following disclaimer.
 *
 *  - Redistributions in binary form must reproduce the above copyright notice,
 *    this list of conditions and the following disclaimer in the documentation
 *    and/or other materials provided with the distribution.
 *
 *  - Neither the name of The University of Chicago nor the names of its
 *    contributors may be used to endorse or promote products derived from this
 *    software withsend specific prior written permission.
 *
 *  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 *  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 *  IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 *  ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE
 *  LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
 *  CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 *  SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 *  INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 *  CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 *  ARISING IN ANY WAY send OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 *  POSSIBILITY OF SUCH DAMAGE.
 *
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>
#include <chidb/log.h>
#include "chidbInt.h"
#include "btree.h"
#include "record.h"
#include "pager.h"
#include "util.h"

#define CHIDB_FILE_HEADER_LEN (100)

/* chidb node type masks */
#define FLAG_TABLE (0x01|0x04)
#define FLAG_INDEX (0x02)
#define FLAG_LEAF (0x08)

static uint8_t pgtypeMap(uint8_t);
static ptrdiff_t getHeaderOffset(npage_t);
static ptrdiff_t getCellOffsetOffset(uint8_t);
static int verifyHeader(uint8_t *);
static void packBTN(BTreeNode *, MemPage *);
static void unpackBTC(uint8_t *, const BTreeCell *);
static size_t getCellSize(const BTreeCell *); 
static int nodeBTCArray(BTreeNode *, BTreeCell **);
static int nodeKeyBSearch(BTreeNode *, BTreeCell *, chidb_key_t, ncell_t *);
static int cellRecordCpy(BTreeCell *, uint8_t **, uint16_t *);

/* Open a B-Tree file
 * This function opens a database file and verifies that the file
 * header is correct. If the file is empty (which will happen
 * if the pager is given a filename for a file that does not exist)
 * then this function will (1) initialize the file header using
 * the default page size and (2) create an empty table leaf node
 * in page 1.
 *
 * Parameters
 * - filename: Database file (might not exist)
 * - db: A chidb struct. Its bt field must be set to the newly
 *       created BTree.
 * - bt: An out parameter. Used to return a pointer to the
 *       newly created BTree.
 *
 * Return
 * - CHIDB_OK: Operation successful
 * - CHIDB_ECORRUPTHEADER: Database file contains an invalid header
 * - CHIDB_ENOMEM: Could not allocate memory
 * - CHIDB_EIO: An I/O error has occurred when accessing the file
 */
int chidb_Btree_open(const char *filename, chidb *db, BTree **bt)
{
    int rc = CHIDB_OK;
    *bt = malloc(sizeof(**bt));
    if (!*bt)
    {
        rc = CHIDB_ENOMEM;
        goto EXIT;
    }
    rc = chidb_Pager_open(&(*bt)->pager, filename);
    if (rc != CHIDB_OK)
    {
        goto EXIT;
    }

    uint8_t header_buf[100] = {0};
    rc = chidb_Pager_readHeader((*bt)->pager, header_buf);
    if (rc != CHIDB_OK) /* Init default header and empty node on page 1. */
    {
        chidb_Pager_setPageSize((*bt)->pager, DEFAULT_PAGE_SIZE);
        npage_t npage;
        rc = chidb_Btree_newNode(*bt, &npage, PGTYPE_TABLE_LEAF);
        if (rc != CHIDB_OK)
        {
            goto EXIT;
        }
        MemPage *page;
        rc = chidb_Pager_readPage((*bt)->pager, 1, &page);
        if (rc != CHIDB_OK)
        {
            goto EXIT;
        }
        strncpy((char *)page->data, "SQLite format 3", 16);
        put2byte(&page->data[16], DEFAULT_PAGE_SIZE);
        page->data[18] = 1;
        page->data[19] = 1;
        page->data[20] = 0;
        page->data[21] = 64;
        page->data[22] = 32;
        page->data[23] = 32;
        put4byte(&page->data[24], 0);
        put4byte(&page->data[32], 0);
        put4byte(&page->data[36], 0);
        put4byte(&page->data[40], 0);
        put4byte(&page->data[44], 1);
        put4byte(&page->data[48], 20000);
        put4byte(&page->data[52], 0);
        put4byte(&page->data[56], 1);
        put4byte(&page->data[60], 0);
        put4byte(&page->data[64], 0);
        chidb_Pager_writePage((*bt)->pager, page);
        chidb_Pager_releaseMemPage((*bt)->pager, page);
        return CHIDB_OK;
    }
    else 
    {
        rc = verifyHeader(header_buf);
        if (rc != CHIDB_OK)
        {
            rc = CHIDB_ECORRUPTHEADER;
            goto EXIT;
        }
        uint16_t page_size = get2byte(header_buf + 16);
        chidb_Pager_setPageSize((*bt)->pager, page_size);
        return CHIDB_OK;
    }
EXIT:
    if (*bt)
    {
        if ((*bt)->pager)
        {
            chidb_Pager_close((*bt)->pager);
        }
        free(*bt);
    }
    return rc;
}

/* Close a B-Tree file
 *
 * This function closes a database file, freeing any resource
 * used in memory, such as the pager.
 *
 * Parameters
 * - bt: B-Tree file to close
 *
 * Return
 * - CHIDB_OK: Operation successful
 * - CHIDB_EIO: An I/O error has occurred when accessing the file
 */
int chidb_Btree_close(BTree *bt)
{
    chidb_Pager_close(bt->pager);
    free(bt);
    return CHIDB_OK;
}

/* Loads a B-Tree node from disk
 *
 * Reads a B-Tree node from a page in the disk. All the information regarding
 * the node is stored in a BTreeNode struct (see header file for more details
 * on this struct). *This is the only function that can allocate memory for
 * a BTreeNode struct*. Always use chidb_Btree_freeMemNode to free the memory
 * allocated for a BTreeNode (do not use free() directly on a BTreeNode variable)
 * Any changes made to a BTreeNode variable will not be effective in the database
 * until chidb_Btree_writeNode is called on that BTreeNode.
 *
 * Parameters
 * - bt: B-Tree file
 * - npage: Page of node to load
 * - btn: Out parameter. Used to return a pointer to newly creater BTreeNode
 *
 * Return
 * - CHIDB_OK: Operation successful
 * - CHIDB_EPAGENO: The provided page number is not valid
 * - CHIDB_ENOMEM: Could not allocate memory
 * - CHIDB_EIO: An I/O error has occurred when accessing the file
 */
int chidb_Btree_getNodeByPage(BTree *bt, npage_t npage, BTreeNode **btn)
{
    /* TODO: Implement error state dependent cleanup for chidb_Pager_readPage.
     * This function needs to handle errors in pager.c:
     * chidb_Pager_readPage does not free the page struct if
     * allocating the page buffer fails. 
     */
    MemPage *page;

    *btn = malloc(sizeof(**btn));
    if (!*btn)
    {
        return CHIDB_ENOMEM;
    }

    int rc = chidb_Pager_readPage(bt->pager, npage, &page);
    if (rc != CHIDB_OK)
    {
        free(*btn);
        *btn = NULL;
        return rc;
    }

    packBTN(*btn, page);
    return CHIDB_OK;
}

/* Frees the memory allocated to an in-memory B-Tree node
 *
 * Frees the memory allocated to an in-memory B-Tree node, and
 * the in-memory page returned by the pages (stored in the
 * "page" field of BTreeNode)
 *
 * Parameters
 * - bt: B-Tree file
 * - btn: BTreeNode to free
 *
 * Return
 * - CHIDB_OK: Operation successful
 */
int chidb_Btree_freeMemNode(BTree *bt, BTreeNode *btn)
{
    int rc = chidb_Pager_releaseMemPage(bt->pager, btn->page);
    free(btn);
    return rc;
}

/* Create a new B-Tree node
 *
 * Allocates a new page in the file and initializes it as a B-Tree node.
 *
 * Parameters
 * - bt: B-Tree file
 * - npage: Out parameter. Returns the number of the page that
 *          was allocated.
 * - type: Type of B-Tree node (PGTYPE_TABLE_INTERNAL, PGTYPE_TABLE_LEAF,
 *         PGTYPE_INDEX_INTERNAL, or PGTYPE_INDEX_LEAF)
 *
 * Return
 * - CHIDB_OK: Operation successful
 * - CHIDB_ENOMEM: Could not allocate memory
 * - CHIDB_EIO: An I/O error has occurred when accessing the file
 */
int chidb_Btree_newNode(BTree *bt, npage_t *npage, uint8_t type)
{
    int rc = CHIDB_OK;
    chidb_Pager_allocatePage(bt->pager, npage);
    rc = chidb_Btree_initEmptyNode(bt, *npage, type);
    return rc;
}

/* Initialize a B-Tree node
 *
 * Initializes a database page to contain an empty B-Tree node. The
 * database page is assumed to exist and to have been already allocated
 * by the pager.
 *
 * Parameters
 * - bt: B-Tree file
 * - npage: Database page where the node will be created.
 * - type: Type of B-Tree node (PGTYPE_TABLE_INTERNAL, PGTYPE_TABLE_LEAF,
 *         PGTYPE_INDEX_INTERNAL, or PGTYPE_INDEX_LEAF)
 *
 * Return
 * - CHIDB_OK: Operation successful
 * - CHIDB_ENOMEM: Could not allocate memory
 * - CHIDB_EIO: An I/O error has occurred when accessing the file
 */
int chidb_Btree_initEmptyNode(BTree *bt, npage_t npage, uint8_t type)
{
    MemPage *page;
    int rc = chidb_Pager_readPage(bt->pager, npage, &page);
    if (rc != CHIDB_OK)
    {
        return rc;
    }

    ptrdiff_t combined_offset = 
        getHeaderOffset(npage) + getCellOffsetOffset(type);
    BTreeNode btn = {
        .page             = page,
        .type             = type,
        .free_offset      = combined_offset,
        .n_cells          = 0,
        .cells_offset     = bt->pager->page_size,
        .right_page       = 0,
        .celloffset_array = page->data + combined_offset
    };
    rc = chidb_Btree_writeNode(bt, &btn);
    chidb_Pager_releaseMemPage(bt->pager, page);
    return CHIDB_OK;
}

/* Write an in-memory B-Tree node to disk
 *
 * Writes an in-memory B-Tree node to disk. To do this, we need to update
 * the in-memory page according to the chidb page format. Since the cell
 * offset array and the cells themselves are modified directly on the
 * page, the only thing to do is to store the values of "type",
 * "free_offset", "n_cells", "cells_offset" and "right_page" in the
 * in-memory page.
 *
 * Parameters
 * - bt: B-Tree file
 * - btn: BTreeNode to write to disk
 *
 * Return
 * - CHIDB_OK: Operation successful
 * - CHIDB_EIO: An I/O error has occurred when accessing the file
 */
int chidb_Btree_writeNode(BTree *bt, BTreeNode *btn)
{
    ptrdiff_t head_offset = getHeaderOffset(btn->page->npage);
    uint8_t *head = &btn->page->data[head_offset];
    head[PGHEADER_PGTYPE_OFFSET] = btn->type;
    head[PGHEADER_ZERO_OFFSET] = 0;
    put2byte(&head[PGHEADER_FREE_OFFSET], btn->free_offset);
    put2byte(&head[PGHEADER_NCELLS_OFFSET], btn->n_cells);
    put2byte(&head[PGHEADER_CELL_OFFSET], btn->cells_offset);
    if (!(btn->type & FLAG_LEAF))
    {
        put4byte(&head[PGHEADER_RIGHTPG_OFFSET], btn->right_page);
    }
    chidb_Pager_writePage(bt->pager, btn->page);
    return CHIDB_OK;
}

/* Read the contents of a cell
 *
 * Reads the contents of a cell from a BTreeNode and stores them in a BTreeCell.
 * This involves the following:
 *  1. Find out the offset of the requested cell.
 *  2. Read the cell from the in-memory page, and parse its
 *     contents (refer to The chidb File Format document for
 *     the format of cells).
 *
 * Parameters
 * - btn: BTreeNode where cell is contained
 * - ncell: Cell number
 * - cell: BTreeCell where contents must be stored.
 *
 * Return
 * - CHIDB_OK: Operation successful
 * - CHIDB_ECELLNO: The provided cell number is invalid
 */
int chidb_Btree_getCell(BTreeNode *btn, ncell_t ncell, BTreeCell *cell)
{
    if (ncell < 0 || ncell >= btn->n_cells)
    {
        return CHIDB_ECELLNO;
    }
    ptrdiff_t cell_offset = get2byte(btn->celloffset_array + 2*ncell);
    uint8_t *head = btn->page->data + cell_offset;
    cell->type = btn->type;
    switch (cell->type)
    {
        case PGTYPE_TABLE_INTERNAL:
            getVarint32(&head[TABLEINTCELL_KEY_OFFSET], &cell->key);
            cell->fields.tableInternal.child_page = 
                get4byte(&head[TABLEINTCELL_CHILD_OFFSET]);
            break;
        case PGTYPE_TABLE_LEAF:
            getVarint32(&head[TABLELEAFCELL_KEY_OFFSET], &cell->key);
            getVarint32(&head[TABLELEAFCELL_SIZE_OFFSET],
                    &cell->fields.tableLeaf.data_size);
            cell->fields.tableLeaf.data =
                &head[TABLELEAFCELL_DATA_OFFSET];
            break;
        case PGTYPE_INDEX_INTERNAL:
            cell->key = get4byte(&head[INDEXINTCELL_KEYIDX_OFFSET]);
            cell->fields.indexInternal.keyPk =
                get4byte(&head[INDEXINTCELL_KEYPK_OFFSET]);
            cell->fields.indexInternal.child_page =
                get4byte(&head[INDEXINTCELL_CHILD_OFFSET]);
            break;
        case PGTYPE_INDEX_LEAF:
            cell->key = get4byte(&head[INDEXLEAFCELL_KEYIDX_OFFSET]);
            cell->fields.indexLeaf.keyPk =
                get4byte(&head[INDEXLEAFCELL_KEYPK_OFFSET]);
            break;
    }
    return CHIDB_OK;
}

/* Insert a new cell into a B-Tree node
 *
 * Inserts a new cell into a B-Tree node at a specified position ncell.
 * This involves the following:
 *  1. Add the cell at the top of the cell area. This involves "translating"
 *     the BTreeCell into the chidb format (refer to The chidb File Format
 *     document for the format of cells).
 *  2. Modify cells_offset in BTreeNode to reflect the growth in the cell area.
 *  3. Modify the cell offset array so that all values in positions >= ncell
 *     are shifted one position forward in the array. Then, set the value of
 *     position ncell to be the offset of the newly added cell.
 *
 * This function assumes that there is enough space for this cell in this node.
 *
 * Parameters
 * - btn: BTreeNode to insert cell in
 * - ncell: Cell number
 * - cell: BTreeCell to insert.
 *
 * Return
 * - CHIDB_OK: Operation successful
 * - CHIDB_ECELLNO: The provided cell number is invalid
 */
int chidb_Btree_insertCell(BTreeNode *btn, ncell_t ncell, BTreeCell *cell)
{
    if (ncell > btn->n_cells)
    {
        return CHIDB_ECELLNO;
    }

    ncell_t old_n_cells = btn->n_cells;
    btn->n_cells ++;
    ptrdiff_t cell_offset = btn->cells_offset -= getCellSize(cell);

    unpackBTC(&btn->page->data[cell_offset], cell);

    if (ncell < old_n_cells)
    {
        memmove(&btn->celloffset_array[2*(ncell+1)],
                &btn->celloffset_array[2*ncell],
                2*(old_n_cells-ncell));
    }
    put2byte(&btn->celloffset_array[2*ncell], cell_offset);
    btn->free_offset += 2;

    return CHIDB_OK;
}

/* Find an entry in a table B-Tree
 *
 * Finds the data associated for a given key in a table B-Tree
 *
 * Parameters
 * - bt: B-Tree file
 * - nroot: Page number of the root node of the B-Tree we want search in
 * - key: Entry key
 * - data: Out-parameter where a copy of the data must be stored
 * - size: Out-parameter where the number of bytes of data must be stored
 *
 * Return
 * - CHIDB_OK: Operation successful
 * - CHIDB_ENOTFOUND: No entry with the given key way found
 * - CHIDB_ENOMEM: Could not allocate memory
 * - CHIDB_EIO: An I/O error has occurred when accessing the file
 */
int chidb_Btree_find(BTree *bt, npage_t nroot, chidb_key_t key, uint8_t **data, uint16_t *size)
{
    uint8_t rc = 0;
    npage_t npage = nroot;
    ncell_t ncell = 0;
    BTreeNode *btn = NULL;
    BTreeCell *btc_arr = NULL;
    struct flags
    {
        bool match : 1;
        bool table : 1;
        bool leaf : 1;
        bool index : 1;
    } flags;

    while (1)
    {
        rc = chidb_Btree_getNodeByPage(bt, npage, &btn);
        if (rc != CHIDB_OK)
            break;
        rc = nodeBTCArray(btn, &btc_arr);
        if (rc != CHIDB_OK)
            break;

        flags.table = btn->type & FLAG_TABLE;
        flags.leaf = btn->type & FLAG_LEAF;
        flags.index = btn->type & FLAG_INDEX;
        flags.match = nodeKeyBSearch(btn, btc_arr, key, &ncell);

        if (flags.match && flags.leaf && flags.table)
        {
            rc = cellRecordCpy(&btc_arr[ncell], data, size);
            break;
        }
        else if (flags.match && flags.index)
        {
            if (flags.leaf)
            {
                key = btc_arr[ncell].fields.indexLeaf.keyPk;
            }
            else
            {
                key = btc_arr[ncell].fields.indexInternal.keyPk;
            }
            npage = nroot;
        }
        else if (!flags.leaf)
        {
            if (ncell == btn->n_cells)
            {
                npage = btn->right_page;
            }
            else if (flags.table)
            {
                npage = btc_arr[ncell].fields.tableInternal.child_page;
            }
            else
            {
                npage = btc_arr[ncell].fields.indexInternal.child_page;
            }
        }
        else
        {
            rc = CHIDB_ENOTFOUND;
            break;
        }

        chidb_Btree_freeMemNode(bt, btn);
        btn = NULL;
        free(btc_arr);
        btc_arr = NULL;
    }

    if (btn)
    {
        chidb_Btree_freeMemNode(bt, btn);
    }
    if (btc_arr)
    {
        free(btc_arr);
    }
    return rc;
}

/* Insert an entry into a table B-Tree
 *
 * This is a convenience function that wraps around chidb_Btree_insert.
 * It takes a key and data, and creates a BTreeCell that can be passed
 * along to chidb_Btree_insert.
 *
 * Parameters
 * - bt: B-Tree file
 * - nroot: Page number of the root node of the B-Tree we want to insert
 *          this entry in.
 * - key: Entry key
 * - data: Pointer to data we want to insert
 * - size: Number of bytes of data
 *
 * Return
 * - CHIDB_OK: Operation successful
 * - CHIDB_EDUPLICATE: An entry with that key already exists
 * - CHIDB_ENOMEM: Could not allocate memory
 * - CHIDB_EIO: An I/O error has occurred when accessing the file
 */
int chidb_Btree_insertInTable(BTree *bt, npage_t nroot, chidb_key_t key, uint8_t *data, uint16_t size)
{
    BTreeCell btc =
    {
        .type = PGTYPE_TABLE_LEAF,
        .key = key,
        .fields.tableLeaf =
        {
            .data_size = size,
            .data = data
        }
    };
    uint8_t rc = chidb_Btree_insert(bt, nroot, &btc);
    return rc;
}


/* Insert an entry into an index B-Tree
 *
 * This is a convenience function that wraps around chidb_Btree_insert.
 * It takes a KeyIdx and a KeyPk, and creates a BTreeCell that can be passed
 * along to chidb_Btree_insert.
 *
 * Parameters
 * - bt: B-Tree file
 * - nroot: Page number of the root node of the B-Tree we want to insert
 *          this entry in.
 * - keyIdx: See The chidb File Format.
 * - keyPk: See The chidb File Format.
 *
 * Return
 * - CHIDB_OK: Operation successful
 * - CHIDB_EDUPLICATE: An entry with that key already exists
 * - CHIDB_ENOMEM: Could not allocate memory
 * - CHIDB_EIO: An I/O error has occurred when accessing the file
 */
int chidb_Btree_insertInIndex(BTree *bt, npage_t nroot, chidb_key_t keyIdx, chidb_key_t keyPk)
{
    BTreeCell btc =
    {
        .type = FLAG_INDEX,
        .key = keyIdx, 
        .fields.indexLeaf.keyPk = keyPk 
    };
    uint8_t rc = chidb_Btree_insert(bt, nroot, &btc);
    return rc;
}


/* Insert a BTreeCell into a B-Tree
 *
 * The chidb_Btree_insert and chidb_Btree_insertNonFull functions
 * are responsible for inserting new entries into a B-Tree, although
 * chidb_Btree_insertNonFull is the one that actually does the
 * insertion. chidb_Btree_insert, however, first checks if the root
 * has to be split (a splitting operation that is different from
 * splitting any other node). If so, chidb_Btree_split is called
 * before calling chidb_Btree_insertNonFull.
 *
 * Parameters
 * - bt: B-Tree file
 * - nroot: Page number of the root node of the B-Tree we want to insert
 *          this cell in.
 * - btc: BTreeCell to insert into B-Tree
 *
 * Return
 * - CHIDB_OK: Operation successful
 * - CHIDB_EDUPLICATE: An entry with that key already exists
 * - CHIDB_ENOMEM: Could not allocate memory
 * - CHIDB_EIO: An I/O error has occurred when accessing the file
 */
int chidb_Btree_insert(BTree *bt, npage_t nroot, BTreeCell *btc)
{
    return CHIDB_OK;
}

/* Insert a BTreeCell into a non-full B-Tree node
 *
 * chidb_Btree_insertNonFull inserts a BTreeCell into a node that is
 * assumed not to be full (i.e., does not require splitting). If the
 * node is a leaf node, the cell is directly added in the appropriate
 * position according to its key. If the node is an internal node, the
 * function will determine what child node it must insert it in, and
 * calls itself recursively on that child node. However, before doing so
 * it will check if the child node is full or not. If it is, then it will
 * have to be split first.
 *
 * Parameters
 * - bt: B-Tree file
 * - nroot: Page number of the root node of the B-Tree we want to insert
 *          this cell in.
 * - btc: BTreeCell to insert into B-Tree
 *
 * Return
 * - CHIDB_OK: Operation successful
 * - CHIDB_EDUPLICATE: An entry with that key already exists
 * - CHIDB_ENOMEM: Could not allocate memory
 * - CHIDB_EIO: An I/O error has occurred when accessing the file
 */
int chidb_Btree_insertNonFull(BTree *bt, npage_t npage, BTreeCell *btc)
{
    return CHIDB_OK;
}


/* Split a B-Tree node
 *
 * Splits a B-Tree node N. This involves the following:
 * - Find the median cell in N.
 * - Create a new B-Tree node M.
 * - Move the cells before the median cell to M (if the
 *   cell is a table leaf cell, the median cell is moved too)
 * - Add a cell to the parent (which, by definition, will be an
 *   internal page) with the median key and the page number of M.
 *
 * Parameters
 * - bt: B-Tree file
 * - npage_parent: Page number of the parent node
 * - npage_child: Page number of the node to split
 * - parent_ncell: Position in the parent where the new cell will
 *                 be inserted.
 * - npage_child2: Out parameter. Used to return the page of the new child node.
 *
 * Return
 * - CHIDB_OK: Operation successful
 * - CHIDB_ENOMEM: Could not allocate memory
 * - CHIDB_EIO: An I/O error has occurred when accessing the file
 */
int chidb_Btree_split(BTree *bt, npage_t npage_parent, npage_t npage_child, ncell_t parent_ncell, npage_t *npage_child2)
{
    return CHIDB_OK;
}

int nodeKeyBSearch(BTreeNode *btn, BTreeCell *btc_arr, chidb_key_t key, ncell_t *ncell)
{
    int left = 0, right = btn->n_cells-1, mid;
    while (left <= right)
    {
        mid = left + (right-left)/2;
        if (btc_arr[mid].key < key)
            left = mid + 1;
        else if (btc_arr[mid].key > key)
            right = mid - 1;
        else
        {
            *ncell = mid;
            return 1;
        }
    }
    /* The left boundary provides a hint to find a child node.
     * Although this assigns a signed int to an unsigned unsigned ncell_t, 
     * boundary <l> will never be negative at any point in the bsearch.
     */
    *ncell = left;
    return 0;
}

/* Rightshift chidb page type codes by 2 for adjacent array indices
 * starting at 0. This allows the pgtype code to determine branching without
 * conditional statements.
 *
 * Parameters:
 *  - type: chidb page type code
 * Return:
 *  - PGTYPE_INDEX_INTERNAL : 0x00
 *  - PGTYPE_TABLE_INTERNAL : 0x01
 *  - PGTYPE_TABLE_LEAF     : 0x02
 *  - PGTYPE_INDEX_LEAF     : 0x03
 */
uint8_t pgtypeMap(uint8_t type)
{
    return type >> 2;
}

/* Avoid clobbering 100B file header on page 1 when converting a note 
 * to/from a buffer & BTreeNode struct.
 */
ptrdiff_t getHeaderOffset(npage_t npage)
{
    return (npage != 1) ? 0 : CHIDB_FILE_HEADER_LEN;
}

/* Given a cell type code, return the offset of the cell offset array
 * in a page of that type. 
 *
 * Note: This value is also equal to the length of the page header.
 */
ptrdiff_t getCellOffsetOffset(uint8_t type)
{
    static const ptrdiff_t tab[2] =
    {
        INTPG_CELLSOFFSET_OFFSET,
        LEAFPG_CELLSOFFSET_OFFSET
    };

    return tab[pgtypeMap(type) >> 1];
}

/* Check for default values for file header fields
 *
 * Parameters:
 * - buf: pointer to 100 byte buffer storing a file header
 *
 * Return:
 * - CHIDB_OK: File header is valid.
 * - CHIDB_ECORRUPTHEADER: File header is not well formed.
 */
int verifyHeader(uint8_t *buf_head)
{
    /* for the current build, these are the only valid values */
    bool invalid_header =
    (
            strncmp((char*)buf_head, "SQLite format 3" , 16) ||
            buf_head[18] != 1                        ||
            buf_head[19] != 1                        ||
            buf_head[20] != 0                        ||
            buf_head[21] != 64                       ||
            buf_head[22] != 32                       ||
            buf_head[23] != 32                       ||
//          get4byte(&buf_head[24]) != 0             ||
            get4byte(&buf_head[32]) != 0             ||
            get4byte(&buf_head[36]) != 0             ||
//          get4byte(&buf_head[40]) != 0             ||
            get4byte(&buf_head[44]) != 1             ||
            /* check_btree_1a.c: test_1a_4 */
            get4byte(&buf_head[48]) != 20000         ||
            get4byte(&buf_head[52]) != 0             ||
            get4byte(&buf_head[56]) != 1             ||
//          get4byte(&buf_head[60]) != 0             ||
            get4byte(&buf_head[64]) != 0
    );
    if (invalid_header)
    {
        return CHIDB_ECORRUPTHEADER;
    }
    else
    {
        return CHIDB_OK;
    }
}

/* Pack a BTreeNode with page header data
 * The purpose of this function is to abstract the task of parsing and casting
 * unstructured data from a buffered page header.
 *
 * Notes:
 * - All resources pointed to by parameters are assumed to be 
 *   already allocated.
 * - The page is assumed to be well-formed.
 * - On leaf nodes, the .right_page field will be set to 0 to indicate
 *   that it is inapplicable.
 * Parameters:
 * - page: the MemPage struct that provides access to a buffered page
 * - btn: the external BTreeNode struct to pack as an out parameter
 */
void packBTN(BTreeNode *btn, MemPage *page)
{
    uint8_t *head = &page->data[getHeaderOffset(page->npage)];
    btn->page = page;
    btn->type = head[PGHEADER_PGTYPE_OFFSET];
    btn->free_offset = get2byte(&head[PGHEADER_FREE_OFFSET]);
    btn->n_cells = get2byte(&head[PGHEADER_NCELLS_OFFSET]);
    btn->cells_offset = get2byte(&head[PGHEADER_CELL_OFFSET]);
    btn->celloffset_array = &head[getCellOffsetOffset(btn->type)];
    if (!(btn->type & FLAG_LEAF))
    {
        btn->right_page = get4byte(&head[PGHEADER_RIGHTPG_OFFSET]);
    }
}

void unpackBTC(uint8_t *head, const BTreeCell *btc)
{
    switch (btc->type)
    {
        case PGTYPE_TABLE_INTERNAL:
            putVarint32(&head[TABLEINTCELL_KEY_OFFSET], btc->key);
            put4byte(&head[TABLEINTCELL_CHILD_OFFSET],
                    btc->fields.tableInternal.child_page);
            return;
        case PGTYPE_TABLE_LEAF:
            putVarint32(&head[TABLELEAFCELL_KEY_OFFSET], btc->key);
            putVarint32(&head[TABLELEAFCELL_SIZE_OFFSET], 
                        btc->fields.tableLeaf.data_size);
            uint8_t *record_head = &head[TABLELEAFCELL_DATA_OFFSET];
            memmove(record_head,
                    btc->fields.tableLeaf.data,
                    btc->fields.tableLeaf.data_size);
            return;
        case PGTYPE_INDEX_INTERNAL:
            put4byte(&head[INDEXINTCELL_KEYIDX_OFFSET], btc->key);
            put4byte(&head[INDEXINTCELL_KEYPK_OFFSET],
                    btc->fields.indexInternal.keyPk);
            put4byte(&head[INDEXINTCELL_CHILD_OFFSET],
                    btc->fields.indexInternal.child_page);
            return;
        case PGTYPE_INDEX_LEAF:
            put4byte(&head[INDEXLEAFCELL_KEYIDX_OFFSET], btc->key);
            put4byte(&head[INDEXLEAFCELL_KEYPK_OFFSET],
                    btc->fields.indexLeaf.keyPk);
            return;
    }
}

/* Using the data of a BTreeCell struct, determine and return
 * the size of the cell encoded in the chidb file format.
 */
size_t getCellSize(const BTreeCell *btc)
{
    const static size_t tab[4] =
    {
        INDEXINTCELL_SIZE,
        TABLEINTCELL_SIZE,
        INDEXLEAFCELL_SIZE,
        TABLELEAFCELL_SIZE_WITHOUTDATA
    };
    int i = pgtypeMap(btc->type);
    size_t size = tab[i];
    if (btc->type & (FLAG_LEAF | FLAG_TABLE))
    {
        size += btc->fields.tableLeaf.data_size;
    }
    
    return size;
}

/* Create an array of all keys of a BTreeNode
 * Parameters:
 *  - btn: pointer to node struct
 *  - key_arr: double pointer to give caller access to array
 * Return:
 *  - CHIDB_OK: Operation successful.
 *  - CHIDB_ENOMEM: Memory allocation failed.
 *  - CHIDB_EEMPTY: Node is empty.
 */
int nodeBTCArray(BTreeNode *btn, BTreeCell **btc_arr)
{
    if (!btn->n_cells)
    {
        return CHIDB_ENOTFOUND;
    }
    *btc_arr = malloc(btn->n_cells * sizeof(**btc_arr));
    if (!(*btc_arr))
    {
        return CHIDB_ENOMEM;
    }
    for (int i=0; i<btn->n_cells; i++)
    {
        int rc = chidb_Btree_getCell(btn, i, &(*btc_arr)[i]);
        if (rc != CHIDB_OK)
        {
            free(*btc_arr);
            return rc;
        }
    }
    return CHIDB_OK;
}

/* Helper function to allocate a buffer and copy a record in an open db page.
 * Parameters:
 *  - btc: the cell from an open internal leaf node to access record.
 */
int cellRecordCpy(BTreeCell *btc, uint8_t **data, uint16_t *size)
{
    *size = btc->fields.tableLeaf.data_size;
    *data = malloc(*size);
    if (!*data)
    {
        return CHIDB_ENOMEM;
    }
    memcpy(*data, btc->fields.tableLeaf.data, *size);  
    return CHIDB_OK;
}
