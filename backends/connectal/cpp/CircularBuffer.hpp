
// Copyright (c) 2016 Massachusetts Institute of Technology

// Permission is hereby granted, free of charge, to any person
// obtaining a copy of this software and associated documentation
// files (the "Software"), to deal in the Software without
// restriction, including without limitation the rights to use, copy,
// modify, merge, publish, distribute, sublicense, and/or sell copies
// of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:

// The above copyright notice and this permission notice shall be
// included in all copies or substantial portions of the Software.

// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
// EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
// MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
// NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
// BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
// ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
// CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.

#ifndef CIRCULAR_BUFFER_HPP
#define CIRCULAR_BUFFER_HPP

#include <list>
#include <ostream>
#include <sstream>
#include <string>
#include <time.h>

class CircularBuffer {
    public:
        CircularBuffer(size_t maxSizeIn) : maxSize(maxSizeIn), entriesToPrint(0), ostreamForPrinting(NULL), data(), firstEntry(true) {}

        void addLine(std::string stringIn) {
            // compute timeDiff and update prevTime
            time_t timeDiff;
            time_t currTime;
            time(&currTime);
            if (!firstEntry) {
                timeDiff = currTime - prevTime;
            } else {
                timeDiff = 0;
                firstEntry = false;
            }
            prevTime = currTime;

            // Add a line to the string when a significant amount of time has
            // elapsed.
            std::ostringstream buffer;
            if (timeDiff > timeThreshold) {
                buffer << "[" << std::dec << timeDiff << " seconds elapsed]" << std::endl;
            }
            buffer << stringIn;

            // Either print the string or add it to a buffer
            if (entriesToPrint > 0) {
                (*ostreamForPrinting) << buffer.str() << std::endl;
                entriesToPrint--;
            } else {
                data.push_back(buffer.str());
                if (data.size() > maxSize) {
                    data.pop_front();
                }
            }
        }

        void printToOStream(std::ostream * o, size_t extraEntriesToPrint) {
            // compute timeDiff and update prevTime (if firstEntry == false)
            time_t currTime;
            time_t timeDiff;
            time(&currTime);
            if (!firstEntry) {
                timeDiff = currTime - prevTime;
                prevTime = currTime;
            } else {
                timeDiff = 0;
            }
            // if this is the first entry, nothing will be done

            // dump the current circular buffer
            while (data.size() > 0) {
                (*o) << data.front() << std::endl;
                data.pop_front();
            }
            if (timeDiff > timeThreshold) {
                (*o) << "[" << std::dec << timeDiff << " seconds elapsed]" << std::endl;
            }

            // if extraEntriesToPrint > 0, then future lines will be printed
            // as they are added
            ostreamForPrinting = o;
            entriesToPrint = extraEntriesToPrint;
        }

    private:
        size_t maxSize;
        size_t entriesToPrint;
        std::ostream *ostreamForPrinting;
        std::list<std::string> data;
        bool firstEntry;
        time_t prevTime;

        const time_t timeThreshold = 3;
};
#endif
