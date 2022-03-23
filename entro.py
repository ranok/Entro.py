#!/usr/bin/env python3

# Python script to manipulate passphrases to analyze entropy
# Author: Jacob Torrey <jacob@thinkst.com>
# (C) 2022 Jacob Torrey

from ast import Lambda, Pass
import json
import math
import string
import itertools
import hashlib
import random
import time
from typing import Dict, List, Callable, Set, Union

HASH_RATE : int = 623000000000

class EntropyBase(object):
    '''Base class to hold shared functionality between the derived classes'''
    def __init__(self):
        self.memoize : Dict = dict()
        self.dict : Dict = dict()

    def poss_to_bits(self, poss) -> float:
        '''Converts a number of possibilities to approx. bits of entropy'''
        return math.log(poss)/math.log(2.0)

    def parse_mask(self, mask : str):
        '''Parse a pattern mask'''
        split = mask.split(' ')
        return split

    def template_to_mask(self, template : str) -> str:
        '''Converts a hashcat template to one for Entro.py'''
        mask = []
        template = template.split('?')[1:]
        for t in template: 
            if t == 'u':
                mask.append('upper')
            elif t == 'l':
                mask.append('lower')
            elif t == 'd':
                mask.append('digit')
            elif t == 's':
                mask.append('punc')
            else:
                mask.append('anyc')
        return ' '.join(mask)

    def hashes_to_str(self, rate : int) -> str:
        '''Converts the raw hash rate to a more readable string in Mh/s'''
        return str(int(rate/1000000))

    def calculate_security(self, possibilities : int):
        '''Calulates the entropy and time to crack n possibilities'''
        hours : float = 1.0 * possibilities / HASH_RATE / (60 * 60)
        days : float = hours / 24.0
        print("Computed %d or approximately 2^%.4f bits of entropy\n" % (possibilities, self.poss_to_bits(possibilities)))
        print("Time to crack: %.2f hrs (%.2f days) @ %s M h/s\n" % (hours, days, self.hashes_to_str(HASH_RATE)))
        return possibilities

    def iter_crack(self, sha1sum : Union[Set, str], pos_mask : str, timeout : int, timef = True) -> int:
        '''Attempts to crack a sha1sum via iterating through dictionary'''
        try:
            start : float = time.time()
            crack_count : int = 0
            mask : List[str] = self.parse_mask(pos_mask)
            lol = []
            for pos in mask:
                if pos not in list(self.memoize.keys()):
                    self.memoize[pos] = self.get_all_pos(pos)
                lol.append(self.memoize[pos])
            for perm in itertools.product(*lol):
                if timeout != 0 and (time.time() - start) >= timeout:
                    return crack_count
                teststr = ''.join(map(str, perm))
                if type(sha1sum) is set:
                    if hashlib.sha1(teststr.encode('utf-8')).hexdigest() in sha1sum:
                        crack_count += 1
                else:
                    if sha1sum == hashlib.sha1(teststr.encode('utf-8')).hexdigest():
                        crack_count += 1
                        if timef:
                            print("Took %d seconds to crack\n" % (time.time() - start))
                        return teststr
            return crack_count
        except KeyboardInterrupt:
            if timef:
                print("Cracked %d passwords in %d seconds\n" % (crack_count, (time.time() - start)))
            return crack_count

    def gen_pass(self, mask) -> str:
        '''Generates a random passphrase from a given mask'''
        mask = self.parse_mask(mask)
        pw : str = ""
        for pos in mask:
            if pos not in list(self.memoize.keys()):
                self.memoize[pos] = self.get_all_pos(pos)
            pw += random.choice(self.memoize[pos])
        return pw

    def load_hashes(self, filename):
        '''Loads in a JSON list of hashes to crack'''
        with open(filename, 'r') as f:
            hashes = json.load(f)
        return set(hashes)

class EntropyAnalyzer(EntropyBase):
    '''Class to hold the functions needed to analyze entropy of given passphrase choices'''
    def __init__(self, dictfile : str):
        '''Initializes the dictionary with passed JSON file'''
        super(EntropyAnalyzer, self).__init__()
        with open(dictfile, 'r') as f:
            self.dict = json.load(f)
        self.add_chars()
        self.memoize = dict()

        self.filters : Dict[Callable[[str], bool]] = dict()
        self.filters['shorter_than_10'] = lambda x: len(x) < 10
        self.filters['shorter_than_8'] = lambda x: len(x) < 8
        self.filters['longer_than_3'] = lambda x: len(x) > 3
        self.filters['alpha_only'] = lambda x: x.isalpha()
        self.filters['ascii_only'] = lambda x: all(ord(c) < 128 for c in x)
        
    def get_pos(self, word : str) -> List[str]:
        '''Return a list of parts-of-speech in the definition of the passed word'''
        wobj = self.dict[word]
        poses = set([])
        for defi in wobj['definitions']:
            poses.add(defi['part_of_speech'])
        return list(poses)

    def filter_dict(self, filter_func : Callable[[str], bool], cull : bool = False) -> Union[None, Dict]:
        '''Filters the dictionary based on passed filtering function on the word'''
        fdict = dict()
        for key, val in list(self.dict.items()):
            if filter_func(key):
                fdict[key] = val
        if cull:
            self.dict = fdict
            self.memoize = dict()
        else:
            return fdict

    def get_num_pos(self, sdict : Union[Dict, None] = None):
        '''Determines the count of each part of speech in the dictionary'''
        if sdict is None:
            sdict = self.dict
        pos_count = {'noun': 0, 'verb': 0, 'adverb': 0, 'adjective': 0, 'pronoun': 0, 'conjunction': 0, 'preposition': 0, 'interjection': 0, 'anyc': 0, 'punc' : 0, 'digit' : 0, 'lower': 0, 'upper' : 0, 'letter': 0}
        for key in list(sdict.items()):
            for pos in self.get_pos(key[0]):
                if pos in pos_count:
                    pos_count[pos] += 1
        pos_count['any'] = len(sdict)
        return pos_count
    
    def calculate_security(self, pos_mask : str) -> int:
        '''Calulates the number of possibilities to guess to find the passphrase matching the part-of-speech mask'''
        pos_count = self.get_num_pos()
        pos_mask = self.parse_mask(pos_mask)
        possibilities : int = 1
        for pos in pos_mask:
            possibilities *= pos_count[pos]
        return super(EntropyAnalyzer, self).calculate_security(possibilities)

    def get_all_pos(self, pos) -> List[str]:
        '''Returns a list of all the words in the dictionary that are the passed part-of-speech'''
        poses : List[str] = []
        for w in list(self.dict.items()):
            w = w[0]
            if pos == "any" or pos in self.get_pos(w):
                poses.append(w)
        return poses
    
    def insert_word_to_dict(self, word : str, poses = List[str]) -> None:
        defis = []
        for pos in poses:
            defis.append({'part_of_speech': pos})
        self.dict[word] = {'definitions': defis}
    
    def add_chars(self) -> None:
        pp = PasswordPattern()
        for typ in pp.memoize.keys():
            if typ == 'letter':
                continue
            if typ == 'any':
                continue
            pos = [typ, 'anyc']
            if typ == 'lower' or typ == 'upper':
                pos.append('letter')
            for c in pp.memoize[typ]:
                self.insert_word_to_dict(c, pos)
            

class PasswordPattern(EntropyBase):
    '''Class to show password patterns'''
    def __init__(self):
        '''Constructor for the password pattern class'''
        super(PasswordPattern, self).__init__()
        self.memoize['lower'] = list(string.ascii_lowercase)
        self.memoize['upper'] = list(string.ascii_uppercase)
        self.memoize['punc'] = list(string.punctuation)
        self.memoize['digit'] = list(string.digits)
        self.memoize['letter'] = list(string.ascii_letters)
        self.memoize['any'] = self.memoize['punc'] + self.memoize['digit'] + self.memoize['letter']

    def calculate_security(self, mask):
        '''Calulates the number of possibilities to guess to find the passphrase matching the part-of-speech mask'''
        mask = self.parse_mask(mask)
        possibilities = 1
        for e in mask:
            possibilities *= len(self.memoize[e])
        return super(PasswordPattern, self).calculate_security(possibilities)
