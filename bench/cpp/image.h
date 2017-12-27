////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	image.h
//
// Project:	vgasim, a Verilator based VGA simulator demonstration
//
// Purpose:	A generic image manipulation class with a few features.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2017, Gisselquist Technology, LLC
//
// This program is free software (firmware): you can redistribute it and/or
// modify it under the terms of  the GNU General Public License as published
// by the Free Software Foundation, either version 3 of the License, or (at
// your option) any later version.
//
// This program is distributed in the hope that it will be useful, but WITHOUT
// ANY WARRANTY; without even the implied warranty of MERCHANTIBILITY or
// FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
// for more details.
//
// You should have received a copy of the GNU General Public License along
// with this program.  (It's in the $(ROOT)/doc directory.  Run make with no
// target there if the PDF file isn't present.)  If not, see
// <http://www.gnu.org/licenses/> for a copy.
//
// License:	GPL, v3, as defined and found on www.gnu.org,
//		http://www.gnu.org/licenses/gpl.html
//
//
////////////////////////////////////////////////////////////////////////////////
//
//
#ifndef	IMAGE_H
#define	IMAGE_H

template<class PIXEL> class IMAGE {
protected:
	unsigned char	*m_buf;
	void	allocbuf(int h, int w);
	void	deallocb(void);
public:
	int	m_height, m_width;
	PIXEL	**m_img;
	PIXEL	*m_data;

	IMAGE(int h, int w);
	IMAGE(IMAGE *imgp);
	~IMAGE() { delete[] m_buf; }
	long	size(void) const { return m_height*m_width; }
	IMAGE *crop(int x, int y, int h, int w);

	void	zeroize(void);
	IMAGE	*copy(void);
	void	flipy(void);
	void	flipx(void);

	int	height(void) const { return m_height; }
	int	cols(void) const { return m_height; }
	int	width(void) const { return m_width; }
	int	rows(void) const { return m_width; }
};

typedef	IMAGE<unsigned char>	UCIMAGE, *PIMAGE;
typedef	IMAGE<int>		IIMAGE, *PIIMAGE;
typedef	IMAGE<double>		DIMAGE, *PDIMAGE;
#ifdef	COMPLEX_H
typedef	IMAGE<COMPLEX>		CIMAGE, *PCIMAGE;
#endif

#endif
